import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H1_R1
import Mathlib

/-! Port of part of the Lennon-Pittel lower-tail proof by Bo Cowgill,
https://github.com/bocowgill/lennon-pittel at commit cf950d0596591bba912b1568aa394f99986f8191,
Copyright 2026 Bo Cowgill, used under the Apache License 2.0.
Changes: modules flattened into one file, comments removed, declarations not needed here dropped,
names adapted to the pinned Mathlib, the marked model renamed and tied to the parent reduction's
definitions (after moon-4's port of the same model for the parent step).
This step is part of the abundance argument of the source. -/


-- StandardExponentialScoreLaw
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace StepA2
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
theorem expMeasure_one_Ioi {L : ℝ} (hL : 0 ≤ L) :
    expMeasure 1 (Ioi L) = ENNReal.ofReal (Real.exp (-L)) := by
  rw [expMeasure_eq_withDensity, withDensity_apply _ measurableSet_Ioi,
    setLIntegral_congr_fun (g := fun x ↦ ENNReal.ofReal (Real.exp (-x))) measurableSet_Ioi
      (fun x hx ↦ by simp [exponentialPDF_of_nonneg (hL.trans hx.le)])]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi L)
    (ae_of_all _ fun x ↦ (Real.exp_pos (-x)).le), integral_exp_neg_Ioi]
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
theorem lintegral_expMeasure_one_exp_neg :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂expMeasure 1) = (1 / 2 : ℝ≥0∞) := by
  rw [lintegral_expMeasure_one _ (by fun_prop)]
  have h (x : ℝ) :
      exponentialPDF 1 x * ENNReal.ofReal (Real.exp (-x)) =
        ENNReal.ofReal (1 / 2) * exponentialPDF 2 x := by
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      congr 1
      simp only [one_mul, ← Real.exp_add]
      rw [show -x + -x = -(2 * x) by ring]
      ring
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), exponentialPDF_of_neg (lt_of_not_ge hx),
        zero_mul, mul_zero]
  simp_rw [h]
  rw [lintegral_const_mul _ (measurable_exponentialPDF 2),
    lintegral_exponentialPDF_eq_one (by norm_num), mul_one,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num
end StepA2
end

-- BoundedProductChernoff
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA2
private theorem exp_le_chord_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.exp x ≤ 1 + (Real.exp 1 - 1) * x := by
  have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (sub_nonneg.mpr hx.2) hx.1 (sub_add_cancel (1 : ℝ) x)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  linarith
private theorem lintegral_exp_bounded_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (g : Ω → ℝ) (hg : Measurable g)
    {B m : ℝ} (hB : 0 < B) (hb : ∀ z, g z ∈ Icc 0 B) (hm : 0 ≤ m)
    (hmass : (∫⁻ z, ENNReal.ofReal (g z) ∂ν) ≤ ENNReal.ofReal m) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (g z / B)) ∂ν) ≤
      ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * m / B)) := by
  let c : ℝ := (Real.exp 1 - 1) / B
  have he : 1 ≤ Real.exp 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num))
  have hc : 0 ≤ c := div_nonneg (sub_nonneg.mpr he) hB.le
  calc
    _ ≤ ∫⁻ z, (1 + ENNReal.ofReal c * ENNReal.ofReal (g z)) ∂ν := by
      apply lintegral_mono
      intro z
      change ENNReal.ofReal (Real.exp (g z / B)) ≤ 1 + ENNReal.ofReal c * ENNReal.ofReal (g z)
      rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one (mul_nonneg hc (hb z).1)]
      apply ENNReal.ofReal_le_ofReal
      rw [show c * g z = (Real.exp 1 - 1) * (g z / B) by dsimp [c]; ring]
      exact exp_le_chord_of_mem_Icc ⟨div_nonneg (hb z).1 hB.le, (div_le_one hB).mpr (hb z).2⟩
    _ = 1 + ENNReal.ofReal c * ∫⁻ z, ENNReal.ofReal (g z) ∂ν := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul _ hg.ennreal_ofReal]
      simp only [lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + ENNReal.ofReal c * ENNReal.ofReal m :=
      add_le_add le_rfl (mul_le_mul_right hmass _)
    _ = ENNReal.ofReal (1 + c * m) := by
      rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one (mul_nonneg hc hm)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [show (Real.exp 1 - 1) * m / B = c * m by dsimp [c]; ring]
      simpa only [add_comm] using Real.add_one_le_exp (c * m)
theorem measure_pi_boundedSum_gt_le {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (g : ∀ i, Ω i → ℝ) (hg : ∀ i, Measurable (g i)) {B : ℝ} (hB : 0 < B)
    (hb : ∀ i z, g i z ∈ Icc 0 B) (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hmass : ∀ i, (∫⁻ z, ENNReal.ofReal (g i z) ∂ν i) ≤ ENNReal.ofReal (m i)) (t : ℝ) :
    (Measure.pi ν) {x | t < ∑ i, g i (x i)} ≤
      ENNReal.ofReal (Real.exp ((-t + (Real.exp 1 - 1) * ∑ i, m i) / B)) := by
  let X (i : ι) (z : Ω i) := ENNReal.ofReal (Real.exp (g i z / B))
  let C (i : ι) := (Real.exp 1 - 1) * m i / B
  let F (x : ∀ i, Ω i) := ENNReal.ofReal (Real.exp ((-t + ∑ i, g i (x i)) / B))
  have hX (i : ι) : Measurable (X i) := (Real.continuous_exp.measurable.comp
    ((hg i).div_const B)).ennreal_ofReal
  have hXpi (i : ι) : Measurable (fun x : ∀ j, Ω j ↦ X i (x i)) :=
    (hX i).comp (measurable_pi_apply i)
  have hfactor (x : ∀ i, Ω i) :
      F x = ENNReal.ofReal (Real.exp (-t / B)) * ∏ i, X i (x i) := by
    unfold F X
    rw [add_div, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, Finset.sum_div,
      Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
  have hF : Measurable F := by
    rw [show F = (fun x ↦ ENNReal.ofReal (Real.exp (-t / B)) * ∏ i, X i (x i)) from
      funext hfactor]
    exact measurable_const.mul (Finset.univ.measurable_prod fun i _ ↦ hXpi i)
  have hmgf (i : ι) :
      (∫⁻ x : ∀ j, Ω j, X i (x i) ∂Measure.pi ν) ≤ ENNReal.ofReal (Real.exp (C i)) := by
    rw [(measurePreserving_eval ν i).lintegral_comp (hX i)]
    exact lintegral_exp_bounded_le (ν i) (g i) (hg i) hB (hb i) (hm i) (hmass i)
  calc
    _ ≤ ∫⁻ x, F x ∂Measure.pi ν := by
      apply meas_le_lintegral₀ hF.aemeasurable
      intro x hx
      have harg : 0 ≤ (-t + ∑ i, g i (x i)) / B :=
        div_nonneg (by simpa only [neg_add_eq_sub] using sub_nonneg.mpr hx.le) hB.le
      simpa only [F, Real.exp_zero, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr harg)
    _ = ENNReal.ofReal (Real.exp (-t / B)) *
        ∏ i, ∫⁻ x : ∀ j, Ω j, X i (x i) ∂Measure.pi ν := by
      simp_rw [hfactor]
      rw [lintegral_const_mul _ (Finset.univ.measurable_prod (fun i _ ↦ hXpi i)),
        lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
          (iIndepFun_pi (fun i ↦ (hX i).aemeasurable)) hXpi]
    _ ≤ ENNReal.ofReal (Real.exp (-t / B)) * ∏ i, ENNReal.ofReal (Real.exp (C i)) :=
      mul_le_mul_right (Finset.prod_le_prod' (fun i _ ↦ hmgf i)) _
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_add]
      simp only [C, ← Finset.sum_div, ← Finset.mul_sum, ← add_div]
end StepA2
end

-- IidScoreRanks
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace StepA2
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
end StepA2
end

-- MarkedCounting
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
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
end StepA2
end

-- ScoreRanks
section
open Function MeasureTheory Set
namespace StepA2
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
end StepA2
end

-- ContinuousScoreBridge
section
open scoped BigOperators ENNReal StepA2
open MeasureTheory Set
namespace StepA2
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
end StepA2
end

-- CoexposureGoodScores
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal StepA2
namespace StepA2
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
theorem ae_unitOpen_scores (n : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∀ r i, x r i ∈ Ioo (0 : ℝ) 1 := by
  have hopen : ∀ᵐ t ∂unitScoreLaw, t ∈ Ioo (0 : ℝ) 1 := by
    rw [unitScoreLaw, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  exact ae_all_iff.2 fun r ↦ ae_all_iff.2 fun i ↦
    (Measure.tendsto_eval_ae_ae (i := r)
      (μ := fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)).eventually
      ((Measure.tendsto_eval_ae_ae (i := i) (μ := fun _ : Fin n ↦ unitScoreLaw)).eventually hopen)
end StepA2
end

-- CoexposureScoreEstimates
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepA2
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
theorem volume_scoreSimplex_coordinate_lower_bound (n : ℕ) (i : Fin n) {s a : ℝ}
    (ha : 0 ≤ a) (has : a ≤ s) :
    volume (scoreSimplex n s ∩ {y | a ≤ y i}) =
      ENNReal.ofReal ((s - a) ^ n / (n.factorial : ℝ)) := by
  have htrans : (fun y : Fin n → ℝ ↦ y + Pi.single i a) ⁻¹'
      (scoreSimplex n s ∩ {y | a ≤ y i}) = scoreSimplex n (s - a) := by
    ext y
    simp only [mem_preimage, mem_inter_iff, scoreSimplex, mem_ofPred_eq, Pi.add_apply,
      Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, ite_true, Pi.single_eq_same]
    constructor
    · rintro ⟨⟨hy, hsum⟩, hi⟩
      refine ⟨fun j ↦ ?_, by linarith⟩
      by_cases h : j = i
      · subst j
        linarith
      · simpa only [Pi.single_eq_of_ne h, add_zero] using hy j
    · rintro ⟨hy, hsum⟩
      refine ⟨⟨fun j ↦ add_nonneg (hy j) ?_, by linarith⟩, by linarith [hy i]⟩
      by_cases h : j = i
      · subst j
        simpa only [Pi.single_eq_same] using ha
      · rw [Pi.single_eq_of_ne h]
  let v : Fin n → ℝ := Pi.single i a
  have hmeasure := (measurePreserving_add_right (volume : Measure (Fin n → ℝ))
    v).measure_preimage_emb (measurableEmbedding_addRight v)
      (scoreSimplex n s ∩ {y | a ≤ y i})
  change volume ((fun y : Fin n → ℝ ↦ y + Pi.single i a) ⁻¹'
      (scoreSimplex n s ∩ {y | a ≤ y i})) = _ at hmeasure
  rw [htrans, volume_scoreSimplex n (sub_nonneg.mpr has)] at hmeasure
  exact hmeasure.symm
theorem volume_scoreSimplex_shell_large_coordinate_le (n : ℕ) (i : Fin n)
    {l u a : ℝ} (hl : 0 < l) (ha : 0 ≤ a) (hau : a * l ≤ u) :
    volume {y : Fin n → ℝ | y ∈ scoreSimplex n u ∧ l ≤ ∑ j, y j ∧
      a < y i / (∑ j, y j)} ≤ ENNReal.ofReal ((u - a * l) ^ n / (n.factorial : ℝ)) := by
  rw [← volume_scoreSimplex_coordinate_lower_bound n i (mul_nonneg ha hl.le) hau]
  apply measure_mono
  intro y hy
  exact ⟨hy.1, (mul_le_mul_of_nonneg_left hy.2.1 ha).trans
    ((lt_div_iff₀ (hl.trans_le hy.2.1)).mp hy.2.2).le⟩
end StepA2
end

-- PittelSimplexRadial
section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace StepA2
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
end StepA2
end

-- PittelSimplexMoments
section
open Filter MeasureTheory Set
open scoped ENNReal BigOperators Topology
namespace StepA2
private noncomputable def pittelAngularSquareScore {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (n : ℝ) * ∑ i, w i ^ 2
section Moments
variable {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
variable (hμ : ∀ᵐ w ∂μ, ∀ i, w i ∈ Icc (0 : ℝ) 1)
variable (hmoment : ∀ a : Fin n → ℕ, (∫ w, ∏ i, w i ^ a i ∂μ) =
  (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
    ((n - 1 + ∑ i, a i).factorial : ℝ))
end Moments
end StepA2
end

-- ExponentialSpouseSquareTail
section
open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
namespace StepA2
local instance : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)
private noncomputable def iidExponentialScoreLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ ↦ expMeasure 1
private noncomputable def expRadiusLowerFactor : ℝ := Real.exp (1 / 2) / 2
theorem expRadiusLowerFactor_pos : 0 < expRadiusLowerFactor := by
  unfold expRadiusLowerFactor
  positivity
theorem expRadiusLowerFactor_lt_one : expRadiusLowerFactor < 1 := by
  have hsq : Real.exp (1 / 2) ^ (2 : ℕ) = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h : Real.exp (1 / 2) < 2 :=
    (sq_lt_sq₀ (Real.exp_pos _).le (by norm_num)).mp
      (hsq.trans_lt (Real.exp_one_lt_three.trans (by norm_num)))
  exact (div_lt_one (by norm_num : 0 < (2 : ℝ))).mpr h
theorem pittelAngularSquareScore_spouseAngle_le_of_totals {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hT : (n : ℝ) / 2 ≤ ∑ i, x i)
    (hS : (∑ i, (x i) ^ (2 : ℕ)) ≤ 6 * (n : ℝ)) :
    pittelAngularSquareScore (spouseAngle x) ≤ 24 := by
  let T := ∑ i, x i
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hhalf : 0 < (n : ℝ) / 2 := by positivity
  have hT' : 0 < T := hhalf.trans_le hT
  calc
    _ = (n : ℝ) * (∑ i, (x i) ^ (2 : ℕ)) / T ^ (2 : ℕ) := by
      simp only [pittelAngularSquareScore, spouseAngle, div_pow, ← Finset.sum_div, T,
        mul_div_assoc]
    _ ≤ ((n : ℝ) * (6 * (n : ℝ))) / ((n : ℝ) / 2) ^ (2 : ℕ) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hS hn'.le)
        (sq_pos_of_pos hhalf) (pow_le_pow_left₀ hhalf.le hT 2)
    _ = _ := by field_simp; ring
theorem measure_iidExponential_radius_lt_half_le (n : ℕ) :
    iidExponentialScoreLaw n {x | (∑ i, x i) < (n : ℝ) / 2} ≤
      ENNReal.ofReal (expRadiusLowerFactor ^ n) := by
  let ν (i : Fin n) := expMeasure (1 : ℝ)
  let g (t : ℝ) := ENNReal.ofReal (Real.exp (-t))
  let F (x : Fin n → ℝ) := ENNReal.ofReal (Real.exp ((n : ℝ) / 2 - ∑ i, x i))
  have hg : Measurable g := by unfold g; fun_prop
  have hf : Measurable F := by unfold F; fun_prop
  have hcoord (i : Fin n) : Measurable (fun x : Fin n → ℝ ↦ g (x i)) :=
    hg.comp (measurable_pi_apply i)
  have hfactor (x : Fin n → ℝ) :
      F x = ENNReal.ofReal (Real.exp ((n : ℝ) / 2)) * ∏ i, g (x i) := by
    unfold F g
    rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Finset.sum_neg_distrib, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
  have hrow (i : Fin n) : (∫⁻ x : Fin n → ℝ, g (x i) ∂Measure.pi ν) =
      ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [(measurePreserving_eval ν i).lintegral_comp hg]
    change (∫⁻ t, ENNReal.ofReal (Real.exp (-t)) ∂expMeasure 1) = _
    rw [lintegral_expMeasure_one_exp_neg, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  change (Measure.pi ν) _ ≤ _
  calc
    _ ≤ ∫⁻ x, F x ∂Measure.pi ν := by
      apply meas_le_lintegral₀ hf.aemeasurable
      intro x hx
      have h : 0 ≤ (n : ℝ) / 2 - ∑ i, x i := sub_nonneg.mpr hx.le
      simpa only [F, Real.exp_zero, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h)
    _ = ENNReal.ofReal (Real.exp ((n : ℝ) / 2)) * (ENNReal.ofReal (1 / 2 : ℝ)) ^ n := by
      simp_rw [hfactor]
      rw [lintegral_const_mul _ (Finset.univ.measurable_prod fun i _ ↦ hcoord i),
        lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
          (iIndepFun_pi fun _ ↦ hg.aemeasurable) hcoord]
      simp only [hrow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = _ := by
      rw [← ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, expRadiusLowerFactor]
      congr 1
      rw [show (n : ℝ) / 2 = (n : ℝ) * (1 / 2) by ring, Real.exp_nat_mul,
        ← mul_pow, mul_one_div]
theorem measure_iidExponential_exists_gt_le (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    iidExponentialScoreLaw n {x | ∃ i, L < x i} ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-L)) := by
  let ν (i : Fin n) := expMeasure (1 : ℝ)
  let E (i : Fin n) := {x : Fin n → ℝ | L < x i}
  have hE (i : Fin n) : (Measure.pi ν) (E i) = ENNReal.ofReal (Real.exp (-L)) := by
    have he := (measurePreserving_eval ν i).measure_preimage
      (measurableSet_Ioi (a := L)).nullMeasurableSet
    exact he.trans (expMeasure_one_Ioi hL)
  have he : {x : Fin n → ℝ | ∃ i, L < x i} = ⋃ i, E i := by
    ext x
    simp only [mem_iUnion, E, mem_ofPred_eq]
  rw [iidExponentialScoreLaw, he]
  refine (measure_iUnion_le _).trans ?_
  rw [tsum_fintype]
  simp only [hE, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ν, le_refl]
private def clippedExponentialSquare (L t : ℝ) : ℝ := min (t ^ (2 : ℕ)) (L ^ (2 : ℕ))
theorem measure_iidExponential_sum_clippedSquare_gt_le (n : ℕ) {L : ℝ} (hL : 0 < L) :
    iidExponentialScoreLaw n {x | 6 * (n : ℝ) < ∑ i, clippedExponentialSquare L (x i)} ≤
      ENNReal.ofReal (Real.exp (- (2 * (n : ℝ)) / L ^ (2 : ℕ))) := by
  let ν (i : Fin n) := expMeasure (1 : ℝ)
  have hg : Measurable (clippedExponentialSquare L) := by unfold clippedExponentialSquare; fun_prop
  have hb (z : ℝ) : clippedExponentialSquare L z ∈ Icc 0 (L ^ (2 : ℕ)) :=
    ⟨le_min (sq_nonneg _) (sq_nonneg _), min_le_right _ _⟩
  have hmass (i : Fin n) :
      (∫⁻ z, ENNReal.ofReal (clippedExponentialSquare L z) ∂ν i) ≤ ENNReal.ofReal (2 : ℝ) := by
    calc
      _ ≤ ∫⁻ z, ENNReal.ofReal (z ^ (2 : ℕ)) ∂ν i :=
        lintegral_mono fun _ ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _)
      _ = _ := lintegral_expMeasure_one_sq.trans (by norm_num)
  refine (measure_pi_boundedSum_gt_le ν (fun _ ↦ clippedExponentialSquare L)
    (fun _ ↦ hg) (sq_pos_of_pos hL) (fun _ ↦ hb) (fun _ ↦ (2 : ℝ))
    (fun _ ↦ by norm_num) hmass _).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (sq_nonneg L)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith only [mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le
    (show 0 ≤ (n : ℝ) * 2 by positivity)]
theorem measure_iidExponential_angleSquare_gt_le {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L) :
    iidExponentialScoreLaw n {x | 24 < pittelAngularSquareScore (spouseAngle x)} ≤
      ENNReal.ofReal (expRadiusLowerFactor ^ n) +
        (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-L)) +
        ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)) / L ^ (2 : ℕ))) := by
  let ν (i : Fin n) := expMeasure (1 : ℝ)
  have hae : ∀ᵐ x ∂iidExponentialScoreLaw n, ∀ i, 0 ≤ x i := ae_all_iff.2 fun i ↦
    (measurePreserving_eval ν i).quasiMeasurePreserving.ae ae_expMeasure_one_nonneg
  let A : Set (Fin n → ℝ) := {x | (∑ i, x i) < (n : ℝ) / 2}
  let B : Set (Fin n → ℝ) := {x | ∃ i, L < x i}
  let C : Set (Fin n → ℝ) := {x | 6 * (n : ℝ) < ∑ i, clippedExponentialSquare L (x i)}
  let U : Set (Fin n → ℝ) := (A ∪ B) ∪ C
  have hsub : {x | 24 < pittelAngularSquareScore (spouseAngle x)}
      ≤ᵐ[iidExponentialScoreLaw n] U := by
    filter_upwards [hae] with x hx hbad
    by_cases hA : x ∈ A
    · exact Or.inl (Or.inl hA)
    by_cases hB : x ∈ B
    · exact Or.inl (Or.inr hB)
    by_cases hC : x ∈ C
    · exact Or.inr hC
    exfalso
    have hT : (n : ℝ) / 2 ≤ ∑ i, x i := le_of_not_gt hA
    have hS : (∑ i, clippedExponentialSquare L (x i)) ≤ 6 * (n : ℝ) := le_of_not_gt hC
    have he : (∑ i, (x i) ^ (2 : ℕ)) = ∑ i, clippedExponentialSquare L (x i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hi : x i ≤ L := le_of_not_gt fun hi ↦ hB ⟨i, hi⟩
      exact (min_eq_left (pow_le_pow_left₀ (hx i) hi 2)).symm
    exact (not_lt_of_ge (pittelAngularSquareScore_spouseAngle_le_of_totals hn x hT
      (he.trans_le hS))) hbad
  exact (measure_mono_ae hsub).trans ((measure_union_le (A ∪ B) C).trans
    (add_le_add ((measure_union_le A B).trans (add_le_add
      (measure_iidExponential_radius_lt_half_le n) (measure_iidExponential_exists_gt_le n hL.le)))
        (measure_iidExponential_sum_clippedSquare_gt_le n hL)))
private theorem eventually_geometric_le_neg_rpow {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, q ^ n ≤ (n : ℝ) ^ (-p) := by
  have hq : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq₀ hq₁)
  have h := (((isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).const_mul_left
    (p / -Real.log q)).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (0 : ℕ), h] with n hn hnlog
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have habs : |p / -Real.log q * Real.log (n : ℝ)| ≤ |(n : ℝ) ^ (1 : ℝ)| := hnlog
  rw [Real.rpow_one, abs_of_nonneg hn'.le] at habs
  have hle : p * Real.log (n : ℝ) ≤ (n : ℝ) * -Real.log q := by
    apply (div_le_iff₀ hq).mp
    rw [mul_div_right_comm]
    exact (le_abs_self _).trans habs
  rw [Real.rpow_def_of_pos hn', ← Real.exp_log hq₀, ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by linarith only [hle])
private theorem size_mul_exp_log_cutoff_eq {n : ℕ} (hn : 0 < n) (p : ℝ) :
    (n : ℝ) * Real.exp (-((p + 2) * Real.log (n : ℝ))) = (n : ℝ) ^ (-(p + 1)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [show -((p + 2) * Real.log (n : ℝ)) = Real.log (n : ℝ) * (-(p + 2)) by ring,
    ← Real.rpow_def_of_pos hn']
  calc
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(p + 2)) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hn', show (1 : ℝ) + -(p + 2) = -(p + 1) by ring]
private theorem eventually_clippedSquare_rate_le (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(2 * (n : ℝ)) /
      ((p + 2) * Real.log (n : ℝ)) ^ (2 : ℕ)) ≤ (n : ℝ) ^ (-(p + 1)) := by
  have h := (((isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) 3 (by norm_num)).const_mul_left
    ((p + 1) * (p + 2) ^ (2 : ℕ))).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (1 : ℕ), h] with n hn hh
  have hn₁ : 1 < (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn₁
  have hL : 0 < (p + 2) * Real.log (n : ℝ) := by positivity
  have habs : |((p + 1) * (p + 2) ^ (2 : ℕ)) * (Real.log (n : ℝ)) ^ (3 : ℝ)| ≤
      |(n : ℝ) ^ (1 : ℝ)| := hh
  rw [Real.rpow_one, abs_of_nonneg hn₀.le, Real.rpow_ofNat] at habs
  have hprod : (p + 1) * Real.log (n : ℝ) * ((p + 2) * Real.log (n : ℝ)) ^ (2 : ℕ) ≤
      2 * (n : ℝ) := by
    calc
      _ = ((p + 1) * (p + 2) ^ (2 : ℕ)) * (Real.log (n : ℝ)) ^ (3 : ℕ) := by ring
      _ ≤ (n : ℝ) := (le_abs_self _).trans habs
      _ ≤ _ := by linarith
  have hd := (le_div_iff₀ (sq_pos_of_pos hL)).mpr hprod
  rw [Real.rpow_def_of_pos hn₀, neg_div]
  exact Real.exp_le_exp.mpr (by linarith only [hd])
theorem eventually_measure_iidExponential_angleSquare_gt_le (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop, iidExponentialScoreLaw n
      {x | 24 < pittelAngularSquareScore (spouseAngle x)} ≤ ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    eventually_geometric_le_neg_rpow expRadiusLowerFactor_pos expRadiusLowerFactor_lt_one (p + 1),
    eventually_clippedSquare_rate_le p hp] with n hn hR hS
  have hn' : 0 < n := by omega
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn'
  have hn₃ : 3 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  let L := (p + 2) * Real.log (n : ℝ)
  have hL : 0 < L := by dsimp [L]; positivity
  let a := (n : ℝ) ^ (-(p + 1))
  have ha : 0 ≤ a := Real.rpow_nonneg hn₀.le _
  have hcap : (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-L)) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hn₀.le,
      size_mul_exp_log_cutoff_eq hn' p]
  refine (measure_iidExponential_angleSquare_gt_le hn' hL).trans ?_
  rw [hcap]
  refine (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hR) le_rfl)
    (ENNReal.ofReal_le_ofReal hS)).trans ?_
  rw [← ENNReal.ofReal_add ha ha, ← ENNReal.ofReal_add (add_nonneg ha ha) ha]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = 3 * a := by ring
    _ ≤ (n : ℝ) * a := mul_le_mul_of_nonneg_right hn₃ ha
    _ = _ := calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(p + 1)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn₀, show (1 : ℝ) + -(p + 1) = -p by ring]
end StepA2
end

-- ExponentialSpouseAngles
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace StepA2
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
end StepA2
end

-- CoexposureScoreRow
section
open Set
open scoped BigOperators
namespace StepA2
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
theorem one_sub_sum_le_scoreRowKernel {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    1 - x * (∑ j ∈ J, y j) ≤ scoreRowKernel J y x := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [scoreRowKernel]
  | @insert j J hj ih =>
      rw [scoreRowKernel, Finset.prod_insert hj, Finset.sum_insert hj]
      have hyj₀ := hy₀ j (Finset.mem_insert_self j J)
      have hyj₁ := hy₁ j (Finset.mem_insert_self j J)
      have hsum : 0 ≤ ∑ k ∈ J, y k :=
        Finset.sum_nonneg fun k hk ↦ hy₀ k (Finset.mem_insert_of_mem hk)
      have hfac : 0 ≤ 1 - x * y j := by
        have := (mul_le_mul_of_nonneg_right hx.2 hyj₀).trans (one_mul (y j) ▸ hyj₁)
        linarith
      calc
        1 - x * (y j + ∑ k ∈ J, y k) ≤ (1 - x * y j) * (1 - x * ∑ k ∈ J, y k) := by
          have hm := mul_nonneg (mul_nonneg hx.1 hyj₀) (mul_nonneg hx.1 hsum)
          nlinarith only [hm]
        _ ≤ (1 - x * y j) * (∏ k ∈ J, (1 - x * y k)) :=
          mul_le_mul_of_nonneg_left (ih
            (fun k hk ↦ hy₀ k (Finset.mem_insert_of_mem hk))
            (fun k hk ↦ hy₁ k (Finset.mem_insert_of_mem hk))) hfac
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
theorem scoreRowMass_lower {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {s : ℝ} (hs : 1 ≤ s) (hsum : ∑ j ∈ J, y j ≤ s) :
    1 / (4 * s) ≤ scoreRowMass J y 0 1 := by
  have hs₀ : 0 < s := lt_of_lt_of_le (by norm_num) hs
  let q : ℝ := 1 / (2 * s)
  have hq₀ : 0 ≤ q := by dsimp [q]; positivity
  have hq₁ : q ≤ 1 := by dsimp [q]; rw [div_le_iff₀ (by positivity)]; linarith
  have hqprod : q * s = 1 / 2 := by dsimp [q]; field_simp
  calc
    1 / (4 * s) = ∫ _ in (0 : ℝ)..q, (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_const]; simp [q]; ring
    _ ≤ ∫ x in (0 : ℝ)..q, scoreRowKernel J y x := by
      refine intervalIntegral.integral_mono_on hq₀ (continuous_const.intervalIntegrable _ _)
        ((continuous_scoreRowKernel J y).intervalIntegrable _ _) fun x hx ↦ ?_
      have hxs : x * (∑ j ∈ J, y j) ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left hsum hx.1).trans
          ((mul_le_mul_of_nonneg_right hx.2 hs₀.le).trans_eq hqprod)
      exact (by linarith : 1 / 2 ≤ 1 - x * (∑ j ∈ J, y j)).trans
        (one_sub_sum_le_scoreRowKernel hy₀ hy₁ ⟨hx.1, hx.2.trans hq₁⟩)
    _ ≤ scoreRowMass J y 0 1 := by
      unfold scoreRowMass
      refine intervalIntegral.integral_mono_interval le_rfl hq₀ hq₁ ?_
        ((continuous_scoreRowKernel J y).intervalIntegrable _ _)
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun x hx ↦
          scoreRowKernel_nonneg hy₀ hy₁ (Ioc_subset_Icc_self hx))
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
theorem scoreRowMass_div_le_exp_tail {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {s a : ℝ} (hs : 2 ≤ s) (hsum₀ : s - 1 ≤ ∑ j ∈ J, y j)
    (hsum₁ : ∑ j ∈ J, y j ≤ s) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    scoreRowMass J y a 1 / scoreRowMass J y 0 1 ≤ 8 * Real.exp (-(s - 1) * a) := by
  have hs₀ : 0 < s := by linarith
  have hs₁ : 0 < s - 1 := by linarith
  have hL := scoreRowMass_lower hy₀ hy₁ (show 1 ≤ s by linarith) hsum₁
  have hL₀ : 0 < 1 / (4 * s) := by positivity
  have hM := scoreRowMass_le_exp_tail hy₀ hy₁ hs₁ hsum₀ ha ha₁ le_rfl
  calc
    _ ≤ (Real.exp (-(s - 1) * a) / (s - 1)) / scoreRowMass J y 0 1 :=
      div_le_div_of_nonneg_right hM (hL₀.le.trans hL)
    _ ≤ (Real.exp (-(s - 1) * a) / (s - 1)) / (1 / (4 * s)) :=
      div_le_div_of_nonneg_left (by positivity) hL₀ hL
    _ = (4 * s / (s - 1)) * Real.exp (-(s - 1) * a) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hs₁).mpr (by linarith))
      (Real.exp_pos _).le
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
theorem scoreRowMass_erase_div_le_exp_tail (y : ι → ℝ) (i : ι)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) {a : ℝ}
    (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    scoreRowMass (Finset.univ.erase i) y a 1 / scoreRowMass (Finset.univ.erase i) y 0 1 ≤
      8 * Real.exp (-((∑ j, y j) - 1) * a) :=
  scoreRowMass_div_le_exp_tail (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hs
    (by rw [sum_erase_eq_total_sub]; linarith [(hy i).2])
    (by rw [sum_erase_eq_total_sub]; linarith [(hy i).1]) ha ha₁
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
end StepA2
end

-- ExposedRotations
section
open StableMarriage
namespace StepA2
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
end StepA2
end

-- CoexposureScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
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
end StepA2
end

-- CoexposureSpouseMarginal
section
open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
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
private theorem lintegral_prod_spouseVectorLaw {n : ℕ} (f : Fin n → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i : Fin n, f i (x i) ∂spouseVectorLaw n) =
      ∏ i : Fin n, ∫⁻ t, f i t ∂unitScoreLaw := by
  have hi := iIndepFun_pi (μ := fun _ : Fin n ↦ unitScoreLaw)
    (X := f) (fun i ↦ (hf i).aemeasurable)
  calc
    _ = ∏ i : Fin n, ∫⁻ x, f i (x i) ∂spouseVectorLaw n :=
      lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hi
        (fun i ↦ (hf i).comp (measurable_pi_apply i))
    _ = _ := Finset.prod_congr rfl fun i _ ↦
      (measurePreserving_eval (fun _ : Fin n ↦ unitScoreLaw) i).lintegral_comp (hf i)
private theorem lintegral_scoreRowKernel_tail {n : ℕ} (J : Finset (Fin n))
    (y : Fin n → ℝ) (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (∫⁻ t in Ioi a, ENNReal.ofReal (scoreRowKernel J y t) ∂unitScoreLaw) =
      ENNReal.ofReal (scoreRowMass J y a 1) := by
  rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioi,
    show Ioi a ∩ Icc (0 : ℝ) 1 = Ioc a 1 by
      ext t
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, ha.trans h.1.le, h.2⟩⟩]
  have hint : IntegrableOn (scoreRowKernel J y) (Ioc a 1) :=
    ((continuous_scoreRowKernel J y).intervalIntegrable a 1).1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc a 1)] scoreRowKernel J y := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc :
      MeasurableSet (Ioc a 1))] with t ht
    unfold scoreRowKernel
    exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr
      ((mul_le_mul_of_nonneg_right ht.2 (hy j).1).trans (by simpa using (hy j).2))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [scoreRowMass, intervalIntegral.integral_of_le ha']
private theorem lintegral_scoreRowKernel_tail_le {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j)
    (i : Fin n) {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ t in Ioi a, ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y t)
        ∂unitScoreLaw) ≤ ENNReal.ofReal (8 * Real.exp (-((∑ j, y j) - 1) * a)) *
      ENNReal.ofReal (scoreRowMass (Finset.univ.erase i) y 0 1) := by
  by_cases ha' : a ≤ 1
  · rw [lintegral_scoreRowKernel_tail _ y hy ha ha', ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ ?_).mp (scoreRowMass_erase_div_le_exp_tail y i hy hs ha ha')
    have hsum : ∑ j ∈ Finset.univ.erase i, y j ≤ ∑ j, y j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ ↦ (hy j).1
    exact (by positivity : 0 < 1 / (4 * ∑ j, y j)).trans_le
      (scoreRowMass_lower (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2)
        ((by norm_num : (1 : ℝ) ≤ 2).trans hs) hsum)
  · have hz : unitScoreLaw.restrict (Ioi a) = 0 := by
      rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioi]
      suffices Ioi a ∩ Icc (0 : ℝ) 1 = ∅ by rw [this, Measure.restrict_empty]
      refine Set.eq_empty_iff_forall_notMem.mpr fun t ht ↦ ha' ?_
      exact ht.1.le.trans ht.2.2
    rw [hz, lintegral_zero_measure]
    exact zero_le
private theorem lintegral_spouseStabilityKernel_tail_le {n : ℕ}
    (y : Fin n → ℝ) (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1)
    (hs : 2 ≤ ∑ j, y j) (i : Fin n) {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ x, {x : Fin n → ℝ | a < x i}.indicator
        (fun x ↦ spouseStabilityKernel x y) x ∂spouseVectorLaw n) ≤
      ENNReal.ofReal (8 * Real.exp (-((∑ j, y j) - 1) * a)) * femaleSpouseStabilityDensity y := by
  classical
  let f (j : Fin n) (t : ℝ) : ℝ≥0∞ :=
    if j = i then (Ioi a).indicator
      (fun t ↦ ENNReal.ofReal (scoreRowKernel (Finset.univ.erase j) y t)) t
    else ENNReal.ofReal (scoreRowKernel (Finset.univ.erase j) y t)
  have hf (j : Fin n) : Measurable (f j) := by
    by_cases h : j = i
    · simpa only [f, if_pos h] using
        (continuous_scoreRowKernel (Finset.univ.erase j) y).measurable.ennreal_ofReal.indicator
          (measurableSet_Ioi (a := a))
    · simpa only [f, if_neg h] using
        (continuous_scoreRowKernel (Finset.univ.erase j) y).measurable.ennreal_ofReal
  have heq (x : Fin n → ℝ) :
      {x : Fin n → ℝ | a < x i}.indicator (fun x ↦ spouseStabilityKernel x y) x =
        ∏ j : Fin n, f j (x j) := by
    by_cases hx : a < x i
    · rw [indicator_of_mem (show x ∈ {x : Fin n → ℝ | a < x i} from hx)]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      by_cases h : j = i
      · subst j
        simp [f, hx]
      · simp [f, h]
    · rw [indicator_of_notMem (show x ∉ {x : Fin n → ℝ | a < x i} from hx)]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [f, hx])).symm
  rw [lintegral_congr heq, lintegral_prod_spouseVectorLaw f hf,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have hother : (∏ j ∈ Finset.univ.erase i, ∫⁻ t, f j t ∂unitScoreLaw) =
      ∏ j ∈ Finset.univ.erase i, ENNReal.ofReal
        (scoreRowMass (Finset.univ.erase j) y 0 1) := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    simpa only [f, if_neg (Finset.mem_erase.mp hj).1] using
      lintegral_scoreRowKernel_unitScoreLaw (Finset.univ.erase j) y hy
  rw [hother]
  calc
    _ ≤ (∏ j ∈ Finset.univ.erase i, ENNReal.ofReal (scoreRowMass (Finset.univ.erase j) y 0 1)) *
        (ENNReal.ofReal (8 * Real.exp (-((∑ j, y j) - 1) * a)) *
          ENNReal.ofReal (scoreRowMass (Finset.univ.erase i) y 0 1)) := by
      gcongr
      simpa only [f, if_pos rfl, lintegral_indicator measurableSet_Ioi] using
        lintegral_scoreRowKernel_tail_le y hy hs i ha
    _ = _ := by
      unfold femaleSpouseStabilityDensity
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      ac_rfl
theorem femaleSpouseTotal_eq_sum_byHusband {n : ℕ} (μ : Matching n) (x : ScoreProfile n) :
    femaleSpouseTotal x μ = ∑ j, femaleSpouseByHusband μ x j :=
  (Equiv.sum_comp μ (femaleSpouseScore x μ)).symm
theorem continuousScoreLaw_stable_and_maleSpouse_gt_le {n : ℕ} (μ : Matching n) (i : Fin n) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        8 * Real.log n / (femaleSpouseTotal x μ - 1) < maleSpouseScore x μ i} ≤
      ENNReal.ofReal (8 * Real.exp (-(8 * Real.log n))) *
        continuousScoreLaw n {x | IsScoreStable x μ} := by
  let a (y : Fin n → ℝ) := 8 * Real.log n / ((∑ j, y j) - 1)
  let B : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {z | 2 ≤ ∑ j, z.2 j ∧ a z.2 < z.1 i}
  have hB : MeasurableSet B := by
    have hsum : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ ∑ j, z.2 j) :=
      Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply j).comp measurable_snd
    have ha : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ a z.2) :=
      measurable_const.div (hsum.sub measurable_const)
    exact (measurableSet_le measurable_const hsum).inter
      (measurableSet_lt ha ((measurable_pi_apply i).comp measurable_fst))
  have hcut : {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        8 * Real.log n / (femaleSpouseTotal x μ - 1) < maleSpouseScore x μ i} =
      {x | IsScoreStable x μ ∧
        ((fun j ↦ maleSpouseScore x μ j), femaleSpouseByHusband μ x) ∈ B} := by
    ext x
    simp [B, a, femaleSpouseTotal_eq_sum_byHusband]
  have hstable : continuousScoreLaw n {x | IsScoreStable x μ} =
      ∫⁻ y, femaleSpouseStabilityDensity y ∂spouseVectorLaw n := by
    simpa using continuousScoreLaw_stable_and_femaleSpouse μ (B := univ) MeasurableSet.univ
  rw [hcut, continuousScoreLaw_stable_and_spouseVectors μ hB,
    lintegral_prod_symm' _ ((measurable_spouseStabilityKernel n).indicator hB), hstable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_spouseVectorLaw_mem_Icc n] with y hy
  by_cases hs : 2 ≤ ∑ j, y j
  · have ha : 0 ≤ a y := div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg n))
      (by linarith)
    have heq (x : Fin n → ℝ) :
        B.indicator (fun z ↦ spouseStabilityKernel z.1 z.2) (x, y) =
          {x : Fin n → ℝ | a y < x i}.indicator (fun x ↦ spouseStabilityKernel x y) x := by
      by_cases hx : a y < x i <;> simp [B, hs, hx]
    rw [lintegral_congr heq]
    have he : -((∑ j, y j) - 1) * a y = -(8 * Real.log n) := by
      dsimp [a]
      field_simp [show (∑ j, y j) - 1 ≠ 0 by linarith]
    simpa only [he] using lintegral_spouseStabilityKernel_tail_le y hy hs i ha
  · have hz : (∫⁻ x, B.indicator (fun z ↦ spouseStabilityKernel z.1 z.2) (x, y)
        ∂spouseVectorLaw n) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      exact Filter.Eventually.of_forall fun x ↦ indicator_of_notMem (fun h ↦ hs h.1) _
    rw [hz]
    exact zero_le
private def badMaleSpouseScores {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
    ∃ i, 8 * Real.log n / (femaleSpouseTotal x μ - 1) < maleSpouseScore x μ i}
private theorem maleSpouseTailCoefficient_eq {n : ℕ} (hn : 0 < n) :
    (n : ℝ≥0∞) * ENNReal.ofReal (8 * Real.exp (-(8 * Real.log n))) =
      ENNReal.ofReal (8 / (n : ℝ) ^ 7) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), Real.exp_neg,
    show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hpos]
  congr 1
  rw [Nat.cast_ofNat, pow_succ]
  field_simp
theorem measure_badMaleSpouseScores_le {n : ℕ} (hn : 0 < n) (μ : Matching n) :
    continuousScoreLaw n (badMaleSpouseScores μ) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 7) * continuousScoreLaw n {x | IsScoreStable x μ} := by
  have he : badMaleSpouseScores μ = ⋃ i : Fin n,
      {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        8 * Real.log n / (femaleSpouseTotal x μ - 1) < maleSpouseScore x μ i} := by
    ext x
    simp only [badMaleSpouseScores, mem_ofPred_eq, mem_iUnion]
    exact ⟨fun ⟨hst, hs, i, hi⟩ ↦ ⟨i, hst, hs, hi⟩,
      fun ⟨i, hst, hs, hi⟩ ↦ ⟨hst, hs, i, hi⟩⟩
  rw [he]
  refine (measure_iUnion_le _).trans ?_
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (8 * Real.exp (-(8 * Real.log n))) *
        continuousScoreLaw n {x | IsScoreStable x μ} :=
      Finset.sum_le_sum fun i _ ↦ continuousScoreLaw_stable_and_maleSpouse_gt_le μ i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
      rw [maleSpouseTailCoefficient_eq hn]
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
theorem sum_measure_badMaleSpouseScores_le {n : ℕ} (hn : 0 < n) :
    (∑ μ : Matching n, continuousScoreLaw n (badMaleSpouseScores μ)) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 7) * ENNReal.ofReal (expectedNumStableMatchings n) := by
  calc
    _ ≤ ∑ μ : Matching n, ENNReal.ofReal (8 / (n : ℝ) ^ 7) *
        continuousScoreLaw n {x | IsScoreStable x μ} :=
      Finset.sum_le_sum fun μ _ ↦ measure_badMaleSpouseScores_le hn μ
    _ = _ := by rw [← Finset.mul_sum, sum_measure_scoreStable_eq_expected]
end StepA2
end

-- CoexposureSpouseShells
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepA2
private def spouseVectorTotal {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  ∑ i, y i
private theorem measurable_spouseVectorTotal (n : ℕ) :
    Measurable (@spouseVectorTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
private def largeRelativeSpouseScoreSet (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ 2 ≤ spouseVectorTotal y ∧ spouseVectorTotal y ≤ n ∧
    ∃ i, 12 * Real.log n / n < y i / spouseVectorTotal y}
private theorem measurableSet_nonnegativeSpouseScores (n : ℕ) :
    MeasurableSet {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)
theorem measurableSet_largeRelativeSpouseScoreSet (n : ℕ) :
    MeasurableSet (largeRelativeSpouseScoreSet n) := by
  unfold largeRelativeSpouseScoreSet
  simp only [ofPred_and, ofPred_exists]
  exact (measurableSet_nonnegativeSpouseScores n).inter
    ((measurableSet_le measurable_const (measurable_spouseVectorTotal n)).inter
      ((measurableSet_le (measurable_spouseVectorTotal n) measurable_const).inter
        (MeasurableSet.iUnion fun i ↦ measurableSet_lt measurable_const
          ((measurable_pi_apply i).div (measurable_spouseVectorTotal n)))))
private theorem exists_shell_index {s b : ℝ} {n : ℕ} (hn : 0 < n) {N : ℕ}
    (hbs : b ≤ s) (hs : (s - b) * (n : ℝ) ≤ (N : ℝ)) :
    ∃ j : Fin (N + 1), b + (j.val : ℝ) / n ≤ s ∧ s ≤ b + (j.val + 1 : ℝ) / n := by
  let j := ⌊(s - b) * (n : ℝ)⌋₊
  have hj : j ≤ N := Nat.floor_le_of_le hs
  have hfloor : (j : ℝ) ≤ (s - b) * (n : ℝ) :=
    Nat.floor_le (mul_nonneg (sub_nonneg.mpr hbs) (Nat.cast_nonneg n))
  have hceil : (s - b) * (n : ℝ) ≤ (j : ℝ) + 1 :=
    (Nat.lt_floor_add_one _).le
  refine ⟨⟨j, Nat.lt_succ_of_le hj⟩, ?_, ?_⟩
  · have h := (div_le_iff₀ (Nat.cast_pos.mpr hn)).2 hfloor
    linarith
  · have h := (le_div_iff₀ (Nat.cast_pos.mpr hn)).2 hceil
    linarith
private theorem lintegral_le_const_mul_volume {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) {f : (Fin n → ℝ) → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ y ∈ S, f y ≤ c) :
    (∫⁻ y in S, f y) ≤ c * volume S := by
  calc
    _ ≤ ∫⁻ _ in S, c := setLIntegral_mono' hS hf
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
private theorem lintegral_spouseShell_le {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) {f : (Fin n → ℝ) → ℝ≥0∞} {l R c : ℝ}
    (hl : 0 < l) (hc : 0 ≤ c) (hL : ∀ y ∈ S, l ≤ spouseVectorTotal y)
    (hV : volume S ≤ ENNReal.ofReal (R ^ n / (n.factorial : ℝ)))
    (hf : ∀ y ∈ S, f y ≤ ENNReal.ofReal (c / spouseVectorTotal y ^ n)) :
    (∫⁻ y in S, f y) ≤ ENNReal.ofReal (c * (R / l) ^ n / (n.factorial : ℝ)) := by
  have hc' : 0 ≤ c / l ^ n := div_nonneg hc (pow_nonneg hl.le _)
  calc
    _ ≤ ENNReal.ofReal (c / l ^ n) * volume S :=
      lintegral_le_const_mul_volume hS fun y hy ↦ (hf y hy).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hc (pow_pos hl _)
          (pow_le_pow_left₀ hl.le (hL y hy) _)))
    _ ≤ ENNReal.ofReal (c / l ^ n) * ENNReal.ofReal (R ^ n / (n.factorial : ℝ)) :=
      by gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul hc', div_pow]; congr 1; ring
private theorem thinShell_ratio_pow_le {n : ℕ} (hn : 0 < n)
    {b l a : ℝ} (hb : 0 < b) (hbl : b ≤ l) (ha : a ≤ 1) :
    ((l + 1 / (n : ℝ) - a * l) / l) ^ n ≤ Real.exp (1 / b - a * n) := by
  have hl := hb.trans_le hbl
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hR : 0 ≤ l + 1 / (n : ℝ) - a * l := by
    linarith [mul_le_of_le_one_left hl.le ha, one_div_nonneg.mpr hn'.le]
  have hdiv : (1 / (n : ℝ)) / l ≤ 1 / (n : ℝ) / b :=
    div_le_div_of_nonneg_left (by positivity) hb hbl
  have hratio : (l + 1 / (n : ℝ) - a * l) / l = 1 + ((1 / (n : ℝ)) / l - a) := by
    field_simp [hl.ne']; ring
  calc
    _ ≤ (Real.exp (1 / (n : ℝ) / b - a)) ^ n := by
      refine pow_le_pow_left₀ (div_nonneg hR hl.le) ?_ n
      rw [hratio]
      linarith [Real.add_one_le_exp (1 / (n : ℝ) / b - a)]
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [hn'.ne']
theorem factorial_mul_lintegral_largeRelativeSpouseScore_le {n : ℕ} (hn : 0 < n)
    (hcut : 12 * Real.log n / (n : ℝ) ≤ 1) {f : (Fin n → ℝ) → ℝ≥0∞}
    (hf : ∀ y ∈ largeRelativeSpouseScoreSet n,
      f y ≤ ENNReal.ofReal (Real.exp 2 / spouseVectorTotal y ^ n)) :
    (n.factorial : ℝ≥0∞) * (∫⁻ y in largeRelativeSpouseScoreSet n, f y) ≤
      ENNReal.ofReal (((n : ℝ) ^ 2 + 1) * n * Real.exp (5 / 2) / (n : ℝ) ^ 12) := by
  let a := 12 * Real.log n / (n : ℝ)
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have ha : 0 ≤ a := by
    have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg h)) hn'.le
  let l (j : Fin (n * n + 1)) : ℝ := 2 + j.val / (n : ℝ)
  let S (q : Fin (n * n + 1) × Fin n) : Set (Fin n → ℝ) :=
    largeRelativeSpouseScoreSet n ∩ {y | y ∈ scoreSimplex n (l q.1 + 1 / (n : ℝ)) ∧
      l q.1 ≤ spouseVectorTotal y ∧ a < y q.2 / spouseVectorTotal y}
  have hS (q : Fin (n * n + 1) × Fin n) : MeasurableSet (S q) := by
    refine (measurableSet_largeRelativeSpouseScoreSet n).inter ?_
    rw [ofPred_and, ofPred_and]
    exact (measurableSet_scoreSimplex _ _).inter
      ((measurableSet_le measurable_const (measurable_spouseVectorTotal n)).inter
        (measurableSet_lt measurable_const
          ((measurable_pi_apply q.2).div (measurable_spouseVectorTotal n))))
  have hcover : largeRelativeSpouseScoreSet n ⊆ ⋃ q, S q := by
    intro y hy
    obtain ⟨hy₀, hy₂, hyn, i, hi⟩ := hy
    have hs : (spouseVectorTotal y - 2) * (n : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right (by linarith) hn'.le
    obtain ⟨j, hj₁, hj₂⟩ := exists_shell_index hn hy₂ hs
    exact mem_iUnion.mpr ⟨(j, i), ⟨hy₀, hy₂, hyn, i, hi⟩, ⟨hy₀, hj₂.trans_eq (by
      dsimp only [l]
      ring)⟩, hj₁, hi⟩
  let c := Real.exp (5 / 2) / (n : ℝ) ^ 12
  have hc₀ : 0 ≤ c := by positivity
  have hlocal (q : Fin (n * n + 1) × Fin n) :
      (∫⁻ y in S q, f y) ≤ ENNReal.ofReal (c / (n.factorial : ℝ)) := by
    have hl₂ : 2 ≤ l q.1 := le_add_of_nonneg_right (by positivity)
    have hl : 0 < l q.1 := by linarith
    have hR : a * l q.1 ≤ l q.1 + 1 / (n : ℝ) :=
      (mul_le_of_le_one_left hl.le hcut).trans (le_add_of_nonneg_right (by positivity))
    have hV := volume_scoreSimplex_shell_large_coordinate_le n q.2 hl ha hR
    refine (lintegral_spouseShell_le (hS q) hl (Real.exp_pos _).le
      (fun y hy ↦ hy.2.2.1) ((measure_mono fun y hy ↦ hy.2).trans hV)
      (fun y hy ↦ hf y hy.1)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hratio := thinShell_ratio_pow_le hn (by norm_num : (0 : ℝ) < 2) hl₂ (show a ≤ 1 from hcut)
    have hlog : a * (n : ℝ) = 12 * Real.log n := div_mul_cancel₀ _ hn'.ne'
    have hcoef : Real.exp 2 * Real.exp (1 / (2 : ℝ) - a * n) = c := by
      dsimp only [c]
      rw [← Real.exp_add, hlog, show 2 + (1 / (2 : ℝ) - 12 * Real.log n) =
        5 / 2 - (12 : ℕ) * Real.log n by ring]
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hn']
    rw [← hcoef]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le) (Nat.cast_nonneg _)
  calc
    _ ≤ (n.factorial : ℝ≥0∞) * ∑ q : Fin (n * n + 1) × Fin n,
          ∫⁻ y in S q, f y := by
      have h := (lintegral_mono_set hcover).trans (by simpa [tsum_fintype] using
        (lintegral_iUnion_le S f : (∫⁻ y in ⋃ q, S q, f y) ≤
          ∑' q, ∫⁻ y in S q, f y))
      exact mul_le_mul_right h _
    _ ≤ (n.factorial : ℝ≥0∞) * ∑ _ : Fin (n * n + 1) × Fin n,
          ENNReal.ofReal (c / (n.factorial : ℝ)) := by
      gcongr with q _
      exact hlocal q
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]
      simp only [← ENNReal.ofReal_natCast]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      dsimp only [c]
      field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]
private def spouseScoreCube (n : ℕ) : Set (Fin n → ℝ) :=
  univ.pi fun _ ↦ Icc (0 : ℝ) 1
private theorem measurableSet_spouseScoreCube (n : ℕ) : MeasurableSet (spouseScoreCube n) :=
  (measurableSet_pi countable_univ).2 (Or.inl fun _ _ ↦ measurableSet_Icc)
private noncomputable def maskedFemaleStabilityDensity (n : ℕ) (y : Fin n → ℝ) :
    ℝ≥0∞ :=
  (spouseScoreCube n).indicator femaleSpouseStabilityDensity y
private theorem femaleSpouseStabilityDensity_eq_ofReal_prod {n : ℕ} {y : Fin n → ℝ}
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    femaleSpouseStabilityDensity y =
      ENNReal.ofReal (∏ i, scoreRowMass (Finset.univ.erase i) y 0 1) := by
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
private theorem sum_stable_femaleSpouse_eq_factorial_mul {n : ℕ}
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B}) =
      (n.factorial : ℝ≥0∞) * (∫⁻ y in B, maskedFemaleStabilityDensity n y) := by
  simp_rw [continuousScoreLaw_stable_and_femaleSpouse _ hB]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [spouseVectorLaw_eq_restrict_volume, Measure.restrict_restrict hB]
  change (n.factorial : ℝ≥0∞) *
    (∫⁻ y in B ∩ spouseScoreCube n, femaleSpouseStabilityDensity y) = _
  unfold maskedFemaleStabilityDensity
  rw [setLIntegral_indicator (measurableSet_spouseScoreCube n),
    inter_comm B (spouseScoreCube n)]
private theorem maskedFemaleStabilityDensity_le_of_largeRelativeSpouseScore {n : ℕ}
    {y : Fin n → ℝ} (hy : y ∈ largeRelativeSpouseScoreSet n) :
    maskedFemaleStabilityDensity n y ≤
      ENNReal.ofReal (Real.exp 2 / spouseVectorTotal y ^ n) := by
  by_cases hcube : y ∈ spouseScoreCube n
  · have hcoord (j : Fin n) : y j ∈ Icc (0 : ℝ) 1 := hcube j (mem_univ j)
    rw [maskedFemaleStabilityDensity, indicator_of_mem hcube,
      femaleSpouseStabilityDensity_eq_ofReal_prod hcoord]
    apply ENNReal.ofReal_le_ofReal
    simpa only [spouseVectorTotal, Fintype.card_fin] using
      scoreRowMass_prod_le_inv_pow y hcoord hy.2.1
  · simp [maskedFemaleStabilityDensity, indicator_of_notMem hcube]
theorem sum_stable_largeRelativeSpouseScore_le {n : ℕ} (hn : 0 < n)
    (hcut : 12 * Real.log n / (n : ℝ) ≤ 1) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ largeRelativeSpouseScoreSet n}) ≤
        ENNReal.ofReal (((n : ℝ) ^ 2 + 1) * n * Real.exp (5 / 2) / (n : ℝ) ^ 12) := by
  rw [sum_stable_femaleSpouse_eq_factorial_mul (measurableSet_largeRelativeSpouseScoreSet n)]
  exact factorial_mul_lintegral_largeRelativeSpouseScore_le hn hcut
    (fun _ ↦ maskedFemaleStabilityDensity_le_of_largeRelativeSpouseScore)
end StepA2
end

-- PittelMeanTail
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
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
end StepA2
end

-- MarkedSpouseAngleComparison
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
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
end StepA2
end

-- ScoreSideSwap
section
open MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepA2
end StepA2
end

-- StableMaleSpouseRowLaw
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
private noncomputable def stableMaleSpouseRowLaw {n : ℕ} (y : Fin n → ℝ) (i : Fin n) : Measure ℝ :=
  unitScoreLaw.withDensity (fun t ↦ ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y t))
private noncomputable def normalizedStableMaleSpouseRowLaw {n : ℕ} (y : Fin n → ℝ) (i : Fin n) :
    Measure ℝ :=
  (stableMaleSpouseRowLaw y i univ)⁻¹ • stableMaleSpouseRowLaw y i
theorem stableMaleSpouseRowLaw_univ {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    stableMaleSpouseRowLaw y i univ =
      ENNReal.ofReal (scoreRowMass (Finset.univ.erase i) y 0 1) := by
  rw [stableMaleSpouseRowLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lintegral_scoreRowKernel_unitScoreLaw _ y hy
theorem stableMaleSpouseRowLaw_isFiniteMeasure {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    IsFiniteMeasure (stableMaleSpouseRowLaw y i) :=
  ⟨(stableMaleSpouseRowLaw_univ y hy i).symm ▸ ENNReal.ofReal_lt_top⟩
theorem stableMaleSpouseRowLaw_univ_pos {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) (i : Fin n) :
    0 < stableMaleSpouseRowLaw y i univ := by
  have hle : ∑ j ∈ Finset.univ.erase i, y j ≤ ∑ j, y j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ ↦ (hy j).1
  have hY : 0 < ∑ j, y j := by linarith
  rw [stableMaleSpouseRowLaw_univ y hy i, ENNReal.ofReal_pos]
  exact (by positivity : 0 < 1 / (4 * ∑ j, y j)).trans_le
    (scoreRowMass_lower (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) (by linarith) hle)
theorem normalizedStableMaleSpouseRowLaw_isProbabilityMeasure {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) (i : Fin n) :
    IsProbabilityMeasure (normalizedStableMaleSpouseRowLaw y i) := by
  have := stableMaleSpouseRowLaw_isFiniteMeasure y hy i
  refine ⟨?_⟩
  rw [normalizedStableMaleSpouseRowLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (stableMaleSpouseRowLaw_univ_pos y hy hs i).ne'
    (measure_ne_top _ _)
theorem ae_normalizedStableMaleSpouseRowLaw_mem_Icc {n : ℕ} (y : Fin n → ℝ) (i : Fin n) :
    ∀ᵐ t ∂normalizedStableMaleSpouseRowLaw y i, t ∈ Icc (0 : ℝ) 1 := by
  have h := withDensity_absolutelyContinuous unitScoreLaw
    (fun t ↦ ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y t))
  exact (Measure.smul_absolutelyContinuous.trans h).ae_le
    (ae_restrict_mem (μ := volume) measurableSet_Icc)
end StepA2
end

-- IndependentFlagLowerTail
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- FiniteProductDensity
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA2
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
theorem pi_withDensity_product (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : ∀ i, Ω i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, IsFiniteMeasure ((ν i).withDensity (f i))] :
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
theorem pi_smul_coordinates (ν : ∀ i, Measure (Ω i)) [∀ i, IsFiniteMeasure (ν i)]
    (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i ↦ c i • ν i) = (∏ i, c i) • Measure.pi ν := by
  let (i : ι) : IsFiniteMeasure (c i • ν i) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (hc i)) (measure_lt_top _ _)⟩
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]
theorem pi_eq_prod_smul_pi_normalized (ν : ∀ i, Measure (Ω i)) [∀ i, IsFiniteMeasure (ν i)]
    (hν : ∀ i, ν i univ ≠ 0) :
    Measure.pi ν = (∏ i, ν i univ) • Measure.pi (fun i ↦ (ν i univ)⁻¹ • ν i) := by
  let ν₀ (i : ι) := (ν i univ)⁻¹ • ν i
  let (i : ι) : IsProbabilityMeasure (ν₀ i) := ⟨by
    change ((ν i univ)⁻¹ • ν i) univ = 1
    rw [Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel (hν i) (measure_ne_top _ _)]⟩
  calc
    Measure.pi ν = Measure.pi (fun i ↦ (ν i univ) • ν₀ i) := by
      congr 1
      funext i
      change ν i = (ν i univ) • ((ν i univ)⁻¹ • ν i)
      rw [smul_smul, ENNReal.mul_inv_cancel (hν i) (measure_ne_top _ _), one_smul]
    _ = _ := pi_smul_coordinates ν₀ _ (fun i ↦ measure_ne_top _ _)
end StepA2
end

-- SmallSpouseTotalLog
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepA2
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
end StepA2
end

-- MeanUpperBound
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepA2
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
theorem eventually_expectedNumStableMatchings_le_sizeSq :
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
end StepA2
end

-- PivotSpouseProductLower
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
private def lowSpouseProductVectorSet (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | 2 ≤ spouseVectorTotal z.2 ∧
    spouseVectorTotal z.1 * spouseVectorTotal z.2 < (n : ℝ) / 128}
private theorem measurable_jointSpouseStabilityKernel (n : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ spouseStabilityKernel z.1 z.2) := by
  unfold spouseStabilityKernel scoreRowKernel
  refine Finset.measurable_prod _ fun i _ ↦ Measurable.ennreal_ofReal ?_
  refine Finset.measurable_prod _ fun j _ ↦ measurable_const.sub ?_
  exact ((measurable_pi_apply i).comp measurable_fst).mul
    ((measurable_pi_apply j).comp measurable_snd)
private theorem ae_spouseVector_nonnegative_unit (n : ℕ) :
    ∀ᵐ y ∂spouseVectorLaw n, ∀ j, y j ∈ Icc (0 : ℝ) 1 :=
  ae_all_iff.2 fun j ↦
    (measurePreserving_eval (fun _ : Fin n ↦ unitScoreLaw) j).quasiMeasurePreserving.ae
      (ae_restrict_mem measurableSet_Icc)
theorem measure_stable_and_spouseVectors_le_of_section {n : ℕ} (μ : Matching n)
    {B : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hB : MeasurableSet B) {a : ℝ≥0∞} (ha : a ≠ ⊤)
    (hsec : ∀ y : Fin n → ℝ, (∀ j, y j ∈ Icc (0 : ℝ) 1) →
      (∫⁻ x, B.indicator (fun z ↦ spouseStabilityKernel z.1 z.2) (x, y) ∂spouseVectorLaw n) ≤
        femaleSpouseStabilityDensity y * a) :
    continuousScoreLaw n
        {x | IsScoreStable x μ ∧
          ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ B} ≤
      continuousScoreLaw n {x | IsScoreStable x μ} * a := by
  rw [continuousScoreLaw_stable_and_spouseVectors μ hB,
    lintegral_prod_symm' _ ((measurable_jointSpouseStabilityKernel n).indicator hB)]
  calc
    _ ≤ ∫⁻ y, femaleSpouseStabilityDensity y * a ∂spouseVectorLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_spouseVector_nonnegative_unit n] with y hy
      exact hsec y hy
    _ = _ := by
      rw [lintegral_mul_const' a _ ha]
      have h := continuousScoreLaw_stable_and_femaleSpouse μ (B := univ) MeasurableSet.univ
      simpa only [mem_univ, and_true, Measure.restrict_univ] using
        congrArg (fun b : ℝ≥0∞ ↦ b * a) h.symm
theorem spouseStabilityKernel_withDensity_eq {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ spouseVectorTotal y) :
    (spouseVectorLaw n).withDensity (fun x ↦ spouseStabilityKernel x y) =
      femaleSpouseStabilityDensity y • Measure.pi (normalizedStableMaleSpouseRowLaw y) := by
  let f (i : Fin n) (t : ℝ) :=
    ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y t)
  let ν := stableMaleSpouseRowLaw y
  let (i : Fin n) : IsFiniteMeasure (ν i) := stableMaleSpouseRowLaw_isFiniteMeasure y hy i
  have hf (i : Fin n) : Measurable (f i) :=
    (continuous_scoreRowKernel _ _).measurable.ennreal_ofReal
  let : ∀ i, IsFiniteMeasure (((fun _ : Fin n ↦ unitScoreLaw) i).withDensity (f i)) :=
    fun i ↦ stableMaleSpouseRowLaw_isFiniteMeasure y hy i
  have htilt : (spouseVectorLaw n).withDensity (fun x ↦ spouseStabilityKernel x y) =
      Measure.pi ν :=
    pi_withDensity_product (fun _ : Fin n ↦ unitScoreLaw) f hf
  have hmass : (∏ i : Fin n, ν i univ) = femaleSpouseStabilityDensity y :=
    Finset.prod_congr rfl fun i _ ↦ stableMaleSpouseRowLaw_univ y hy i
  rw [htilt, pi_eq_prod_smul_pi_normalized ν
    (fun i ↦ (stableMaleSpouseRowLaw_univ_pos y hy hs i).ne'), hmass]
  rfl
end StepA2
end

-- PivotForwardRevealCell
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
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
end StepA2
end

-- PivotReverseEligibility
section
open MeasureTheory Set
open scoped ENNReal
namespace StepA2
end StepA2
end

-- PivotReverseRowLaw
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
variable {ι : Type*}
end StepA2
end

-- ReverseSuccessorIncrement
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
variable {ι : Type*}
end StepA2
end

-- ReverseCompatibilityRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- PivotReverseRelaxedColumn
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- ReverseSuccessorRotation
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
end StepA2
end

-- PivotReverseScoreSuccessor
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- PivotRelaxedArcEvents
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- FinitePrerequisites
section
namespace StepA2
end StepA2
end

-- RotationDiamond
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ σ : Equiv.Perm (Fin n)}
end StepA2
end

-- ManOptimal
section
open StableMarriage
open scoped BigOperators
namespace StepA2
variable {n : ℕ}
private def MenWeaklyPrefer (p : Profile n) (μ ν : Matching n) : Prop :=
  ∀ m, p.manRank m (μ m) ≤ p.manRank m (ν m)
private def IsManOptimal (p : Profile n) (μ : Matching n) : Prop :=
  IsStable p μ ∧ ∀ ν, IsStable p ν → MenWeaklyPrefer p μ ν
end StepA2
end

-- RotationCycle
section
namespace StepA2
open Function
end StepA2
end

-- TargetSuccessor
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ ν : Matching n}
end StepA2
end

-- RotationReachability
section
open scoped BigOperators
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n}
private inductive RotationSequence (p : Profile n) :
    Matching n → List (Equiv.Perm (Fin n)) → Matching n → Prop where
  | nil {μ : Matching n} (hμ : IsStable p μ) : RotationSequence p μ [] μ
  | cons {μ ν : Matching n} {ρ : Equiv.Perm (Fin n)} {rs : List (Equiv.Perm (Fin n))}
      (hμ : IsStable p μ) (hρ : IsExposedRotation p μ ρ)
      (rest : RotationSequence p (eliminateRotation μ ρ) rs ν) :
      RotationSequence p μ (ρ :: rs) ν
end StepA2
end

-- RotationLabels
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n}
private structure RotationLabel (n : ℕ) where
  cycle : Equiv.Perm (Fin n)
  oldPartner : Fin n → Option (Fin n)
private def rotationLabel (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : RotationLabel n :=
  ⟨ρ, fun m ↦ if ρ m = m then none else some (μ m)⟩
private def rotationLabels : Matching n → List (Equiv.Perm (Fin n)) → List (RotationLabel n)
  | _, [] => []
  | μ, ρ :: rs => rotationLabel μ ρ :: rotationLabels (eliminateRotation μ ρ) rs
end StepA2
end

-- RotationPathIndependence
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n}
end StepA2
end

-- RotationTrace
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n}
namespace RotationSequence
variable {μ ν τ : Matching n} {rs ss : List (Equiv.Perm (Fin n))}
end RotationSequence
end StepA2
end

-- RotationIdeals
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
private def Rotation (p : Profile n) (μ₀ : Matching n) :=
  {r : RotationLabel n // ∃ ν rs, RotationSequence p μ₀ rs ν ∧ r ∈ rotationLabels μ₀ rs}
end StepA2
end

-- CoexposedRotations
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
end StepA2
end

-- CoexposedRotationMultiplicity
section
open StableMarriage
open scoped BigOperators
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ : Matching n}
end StepA2
end

-- CoexposureCycleMoment
section
open StableMarriage MeasureTheory
open scoped BigOperators ENNReal
namespace StepA2
private def RealizesSuccessorPermutation {n : ℕ} (p : Profile n) (M σ : Matching n) : Prop :=
  ∀ i ∈ σ.support, IsSuccessor p M i (M (σ i))
end StepA2
end

-- PivotReverseMaskJointLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- RowCompetition
section
open Set
open scoped BigOperators
namespace StepA2
variable {ι : Type*} {J : Finset ι} {a : ι → ℝ} {A b : ℝ}
private theorem rowCompetition_integral_rpow (hb : 0 < b) (hA : 0 ≤ A) :
    (∫ z in (0 : ℝ)..1, (1 - b * z) ^ (A / b)) =
      (1 - (1 - b) ^ (1 + A / b)) / (A + b) := by
  have hr : 0 ≤ A / b := div_nonneg hA hb.le
  have h := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1)
    (f := fun x : ℝ ↦ x ^ (A / b)) b 1
  simp only [mul_one, mul_zero, sub_zero] at h
  rw [integral_rpow (Or.inl (by linarith : -1 < A / b)), Real.one_rpow,
    add_comm (A / b) 1] at h
  apply (eq_div_iff (by positivity : A + b ≠ 0)).2
  have h' := (eq_div_iff (by positivity : 1 + A / b ≠ 0)).1 h
  rw [show A + b = b * (1 + A / b) by field_simp; ring]
  linear_combination h'
private theorem rowCompetition_endpoint_le_exp (hb : 0 < b) (hb₁ : b ≤ 1) (hA : 0 ≤ A) :
    (1 - b) ^ (1 + A / b) ≤ Real.exp (-A) := by
  have hr : 0 ≤ 1 + A / b := by positivity
  calc
    (1 - b) ^ (1 + A / b) ≤ Real.exp (-b) ^ (1 + A / b) :=
      Real.rpow_le_rpow (sub_nonneg.mpr hb₁) (by linarith [Real.add_one_le_exp (-b)]) hr
    _ = Real.exp (-b * (1 + A / b)) := (Real.exp_mul ..).symm
    _ ≤ Real.exp (-A) := by
      apply Real.exp_le_exp.mpr
      rw [show -b * (1 + A / b) = -b - A by field_simp; ring]
      linarith
theorem scoreRowMass_lower_power (hb : 0 < b) (hb1 : b ≤ 1)
    (ha : ∀ j ∈ J, a j ∈ Icc 0 b) (hsum : ∑ j ∈ J, a j ≤ A) :
    (1 - (1 - b) ^ (1 + A / b)) / (A + b) ≤ scoreRowMass J a 0 1 := by
  have hA := (Finset.sum_nonneg fun j hj ↦ (ha j hj).1).trans hsum
  have hcont : Continuous fun t : ℝ ↦ (1 - b * t) ^ (A / b) :=
    (continuous_const.sub (continuous_const.mul continuous_id)).rpow_const
      fun _ ↦ Or.inr (div_nonneg hA hb.le)
  rw [← rowCompetition_integral_rpow hb hA]
  refine intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _)
    ((continuous_scoreRowKernel J a).intervalIntegrable _ _) fun t ht ↦ ?_
  have hbt : b * t ≤ 1 := (mul_le_of_le_one_left ht.1 hb1).trans ht.2
  have hbase := sub_nonneg.mpr hbt
  have hweight (j) (hj : j ∈ J) : 0 ≤ a j / b := div_nonneg (ha j hj).1 hb.le
  calc
    (1 - b * t) ^ (A / b) ≤ (1 - b * t) ^ ((∑ j ∈ J, a j) / b) :=
      Real.rpow_le_rpow_of_exponent_ge' hbase (sub_le_self _ (mul_nonneg hb.le ht.1))
        (div_nonneg (Finset.sum_nonneg fun j hj ↦ (ha j hj).1) hb.le)
        (div_le_div_of_nonneg_right hsum hb.le)
    _ = ∏ j ∈ J, (1 - b * t) ^ (a j / b) := by
      rw [Finset.sum_div, Real.rpow_sum_of_nonneg hbase hweight]
    _ ≤ scoreRowKernel J a t := by
      refine Finset.prod_le_prod (fun j _ ↦ Real.rpow_nonneg hbase _) fun j hj ↦ ?_
      have h := rpow_one_add_le_one_add_mul_self (s := -(b * t)) (by linarith only [hbt])
        (hweight j hj) ((div_le_one hb).mpr (ha j hj).2)
      rw [← sub_eq_add_neg] at h
      refine h.trans_eq ?_
      field_simp
      ring
theorem scoreRowMass_lower_bounded (hb : 0 < b) (hb1 : b ≤ 1)
    (ha : ∀ j ∈ J, a j ∈ Icc 0 b) (hA : 0 < A) (hsum : ∑ j ∈ J, a j ≤ A) :
    (1 - Real.exp (-A)) / (A + b) ≤ scoreRowMass J a 0 1 :=
  (div_le_div_of_nonneg_right (sub_le_sub_left (rowCompetition_endpoint_le_exp hb hb1 hA.le) 1)
    (add_nonneg hA.le hb.le)).trans (scoreRowMass_lower_power hb hb1 ha hsum)
end StepA2
end

-- ReverseArcRelativeLower
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- ReverseIIDLabelGood
section
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace StepA2
section Measures
variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]
variable [Fintype α] [DiscreteMeasurableSpace α]
end Measures
end StepA2
end

-- ReverseCycleLabelMultiplicity
section
open scoped BigOperators ENNReal
namespace StepA2
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {k : ℕ} {A : Finset α} {F : α → Finset α}
end StepA2
end

-- ReverseDerangementFraction
section
open scoped ENNReal
namespace StepA2
end StepA2
end

-- PivotReverseMaskLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
private noncomputable def reverseSpouseWeights {n : ℕ} (μ : Matching n) (d : DiagonalScorePairs n) :
    Fin n → ℝ≥0∞ := fun j ↦
  ENNReal.ofReal ((diagonalPairAt d (μ.symm j)).1 / ∑ i, (diagonalPairAt d i).1)
end StepA2
end

-- PivotReverseCompetitorMass
section
open StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
private noncomputable def forwardMaskOmittedMass {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) : ℝ :=
  ∑ i : {i : Fin n // i ≠ j}, if flag ⟨(i.val, j), i.property⟩ then
    (diagonalPairAt d i.val).1 else 0
end StepA2
end

-- PivotForwardMaskProbability
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- WeightedBoolProductTail
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- PivotEligibleMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- PivotForwardRevealRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
private abbrev ForwardRevealedMaleScores {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  ForwardActiveCellIndex flag → ℝ
private abbrev ForwardInactiveColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  (i : Fin n) → ForwardInactiveColumnIndex flag i → ℝ × ℝ
private def forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    OffDiagonalScorePairs n → ForwardRevealedMaleScores flag × ForwardInactiveColumns flag :=
  Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag
end StepA2
end

-- PivotForwardPivotReadout
section
open MeasureTheory Set StableMarriage
namespace StepA2
end StepA2
end

-- SingletonIdealAnchor
section
namespace StepA2
variable {α : Type*} [PartialOrder α]
end StepA2
end

-- SingletonRotationAnchor
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
end StepA2
end

-- ReverseRotationIdeals
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n} {σ : Equiv.Perm (Fin n)}
end StepA2
end

-- PivotCrossBlocker
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n} {A N : Matching n} {ρ : Equiv.Perm (Fin n)}
end StepA2
end

-- PivotReversePermutationCompatibility
section
open StableMarriage
namespace StepA2
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
end StepA2
end

-- ReverseSupportWeightUpper
section
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- PivotCompatibilityLoss
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- UndoMaximalSubset
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n}
end StepA2
end

-- RotationUndoSequences
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {hopt : IsManOptimal p μ₀}
end StepA2
end

-- PivotIncidenceCounting
section
open StableMarriage
open scoped BigOperators
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ₀ ν μ : Matching n} {hopt : IsManOptimal p μ₀}
namespace PivotDecoration
variable {K : ℕ} {r : Rotation p μ₀}
end PivotDecoration
end StepA2
end

-- PivotCompatibleLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- ReverseIncrementColumnTail
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
variable {ι : Type*}
end StepA2
end

-- PivotReverseIncrementFilter
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
private noncomputable def reverseIncrementCutoff (n : ℕ) (X : ℝ) : ℝ := 16 * Real.log (n : ℝ) / X
end StepA2
end

-- PivotReverseFilteredCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
private def shortCycleCapBad (L : ℕ) (T : Multiset ℕ) : Prop :=
  (3 / 2 : ℝ) * Real.log (L : ℝ) < ((T.filter (· ≤ L)).card : ℝ)
end StepA2
end

-- ReverseColoredPermutations
section
open scoped BigOperators
namespace StepA2
end StepA2
end

-- CoexposureGaussianSum
section
open scoped BigOperators ENNReal
open Finset Filter
namespace StepA2
private theorem sum_cast_range_gaussian (j : ℕ) :
    (∑ i ∈ range j, (i : ℝ)) = (j : ℝ) * ((j : ℝ) - 1) / 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    ring
theorem descFactorial_div_pow_le_exp {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (n.descFactorial j : ℝ) / (n : ℝ) ^ j ≤
      Real.exp (-((j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ)))) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hi (i : ℕ) (h : i ∈ range j) : i ≤ n := (mem_range.mp h).le.trans hj
  have hpow : (n : ℝ) ^ j = ∏ _i ∈ range j, (n : ℝ) := by simp
  calc
    _ = ∏ i ∈ range j, (1 - (i : ℝ) / (n : ℝ)) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, hpow, ← prod_div_distrib]
      refine prod_congr rfl fun i h ↦ ?_
      rw [Nat.cast_sub (hi i h)]
      field_simp
    _ ≤ ∏ i ∈ range j, Real.exp (-((i : ℝ) / (n : ℝ))) :=
      prod_le_prod (fun i h ↦ sub_nonneg.mpr ((div_le_one (by positivity)).mpr
        (Nat.cast_le.mpr (hi i h)))) fun i _ ↦ by
          simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-((i : ℝ) / (n : ℝ)))
    _ = _ := by
      rw [← Real.exp_sum, sum_neg_distrib, ← sum_div, sum_cast_range_gaussian]
      congr 1
      ring
private noncomputable def coexposureEsymm {ι : Type*} (s : Finset ι) (j : ℕ) (w : ι → ℝ) : ℝ :=
  ∑ t ∈ s.powersetCard j, ∏ i ∈ t, w i
private theorem coexposureEsymm_zero {ι : Type*} (s : Finset ι) (w : ι → ℝ) :
    coexposureEsymm s 0 w = 1 := by simp [coexposureEsymm]
private theorem coexposureEsymm_congr {ι : Type*} {s : Finset ι} (j : ℕ) {w v : ι → ℝ}
    (h : ∀ i ∈ s, w i = v i) : coexposureEsymm s j w = coexposureEsymm s j v :=
  sum_congr rfl fun _ ht ↦ prod_congr rfl fun i hi ↦ h i ((mem_powersetCard.mp ht).1 hi)
private theorem coexposureEsymm_nonneg {ι : Type*} (s : Finset ι) (j : ℕ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ coexposureEsymm s j w :=
  sum_nonneg fun _ _ ↦ prod_nonneg fun i _ ↦ hw i
private theorem coexposureEsymm_insert_succ {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι} (ha : a ∉ s) (j : ℕ) (w : ι → ℝ) :
    coexposureEsymm (insert a s) (j + 1) w =
      coexposureEsymm s (j + 1) w + w a * coexposureEsymm s j w := by
  have hnot (k : ℕ) {t : Finset ι} (ht : t ∈ s.powersetCard k) : a ∉ t :=
    fun hat ↦ ha ((mem_powersetCard.mp ht).1 hat)
  have hdisj : Disjoint (s.powersetCard (j + 1)) ((s.powersetCard j).image (insert a)) :=
    disjoint_left.mpr fun t ht ht' ↦ by
      obtain ⟨u, _, rfl⟩ := mem_image.mp ht'
      exact hnot (j + 1) ht (mem_insert_self a u)
  have hinj : Set.InjOn (insert a) (s.powersetCard j : Set (Finset ι)) := by
    intro t ht u hu he
    have he' := congrArg (fun v : Finset ι ↦ v.erase a) he
    simpa only [erase_insert (hnot j ht), erase_insert (hnot j hu)] using he'
  unfold coexposureEsymm
  rw [powersetCard_succ_insert ha j, sum_union hdisj, sum_image hinj, mul_sum]
  congr 1
  exact sum_congr rfl fun t ht ↦ prod_insert (hnot j ht)
private theorem coexposureEsymm_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ) :
    coexposureEsymm s 1 w = ∑ i ∈ s, w i := by
  induction s using Finset.induction_on with
  | empty => simp [coexposureEsymm, powersetCard_one]
  | @insert a s ha ih =>
    rw [coexposureEsymm_insert_succ ha 0, coexposureEsymm_zero, mul_one,
      ih, sum_insert ha, add_comm]
private theorem coexposureEsymm_insert_insert {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a b : ι} (ha : a ∉ insert b s) (hb : b ∉ s) (j : ℕ) (w : ι → ℝ) :
    coexposureEsymm (insert a (insert b s)) (j + 2) w =
      coexposureEsymm s (j + 2) w + (w a + w b) * coexposureEsymm s (j + 1) w +
        w a * w b * coexposureEsymm s j w := by
  rw [show j + 2 = (j + 1) + 1 by rfl, coexposureEsymm_insert_succ ha,
    coexposureEsymm_insert_succ hb, coexposureEsymm_insert_succ hb]
  ring
private abbrev coexposureSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}
private theorem exists_coexposure_smoothing {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (hw : w ∈ coexposureSimplex ι) {a b : ι} (hab : a ≠ b) (hne : w a ≠ w b)
    (j : ℕ) :
    ∃ v ∈ coexposureSimplex ι, coexposureEsymm univ j w ≤ coexposureEsymm univ j v ∧
      (∑ i, (v i) ^ 2) < ∑ i, (w i) ^ 2 := by
  classical
  let t := (univ.erase a).erase b
  have hat : a ∉ t := fun h ↦ notMem_erase a _ (mem_erase.mp h).2
  have hbt : b ∉ t := notMem_erase _ _
  have hat' : a ∉ insert b t := by simp [hab, hat]
  have hdecomp : insert a (insert b t) = univ := by
    ext i
    by_cases hi : i = a
    · simp [hi]
    by_cases hi' : i = b
    · simp [hi']
    simp [t, hi, hi']
  have hsplit (f : ι → ℝ) : (∑ i, f i) = f a + f b + ∑ i ∈ t, f i := by
    rw [← hdecomp, sum_insert hat', sum_insert hbt]
    ring
  let c := (w a + w b) / 2
  let v := fun i ↦ if i = a ∨ i = b then c else w i
  have hva : v a = c := by simp [v]
  have hvb : v b = c := by simp [v]
  have hvt (i : ι) (hi : i ∈ t) : v i = w i := by
    have hia : i ≠ a := fun h ↦ hat (h ▸ hi)
    have hib : i ≠ b := fun h ↦ hbt (h ▸ hi)
    simp [v, hia, hib]
  have hsum : ∑ i, v i = 1 := by
    rw [← hw.2, hsplit v, hsplit w, hva, hvb, sum_congr rfl hvt]
    dsimp [c]
    ring
  have hnonneg (i : ι) : 0 ≤ v i := by
    dsimp [v, c]
    split_ifs <;> positivity [hw.1 i, hw.1 a, hw.1 b]
  refine ⟨v, ⟨hnonneg, hsum⟩, ?_, ?_⟩
  · cases j with
    | zero => simp only [coexposureEsymm_zero, le_refl]
    | succ j =>
      cases j with
      | zero =>
        rw [show 0 + 1 = 1 by rfl, coexposureEsymm_one, coexposureEsymm_one, hw.2, hsum]
      | succ j =>
        change coexposureEsymm univ (j + 2) w ≤ coexposureEsymm univ (j + 2) v
        rw [← hdecomp, coexposureEsymm_insert_insert hat' hbt,
          coexposureEsymm_insert_insert hat' hbt,
          coexposureEsymm_congr (j + 2) hvt, coexposureEsymm_congr (j + 1) hvt,
          coexposureEsymm_congr j hvt, hva, hvb]
        have hcc : c + c = w a + w b := by dsimp [c]; ring
        have hm : w a * w b ≤ c * c := by dsimp [c]; nlinarith [sq_nonneg (w a - w b)]
        rw [hcc]
        gcongr
        exact coexposureEsymm_nonneg t j hw.1
  · rw [hsplit (fun i ↦ (v i) ^ 2), hsplit (fun i ↦ (w i) ^ 2)]
    simp only [hva, hvb]
    rw [sum_congr rfl (fun i hi ↦ congrArg (fun z : ℝ ↦ z ^ 2) (hvt i hi))]
    dsimp [c]
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]
theorem coexposureEsymm_le_uniform {n : ℕ} (hn : 0 < n) (j : ℕ) {w : Fin n → ℝ}
    (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) :
    coexposureEsymm univ j w ≤ (n.choose j : ℝ) * (1 / (n : ℝ)) ^ j := by
  classical
  let E := coexposureEsymm (univ : Finset (Fin n)) j
  have hE : Continuous E :=
    continuous_finsetSum _ fun t _ ↦ continuous_finsetProd _ fun i _ ↦ continuous_apply i
  let S := coexposureSimplex (Fin n)
  have hS : IsCompact S := by
    exact isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin n)
  have hwS : w ∈ S := ⟨hw₀, hw⟩
  obtain ⟨u, hu, humax⟩ := hS.exists_isMaxOn ⟨w, hwS⟩ hE.continuousOn
  let T := S ∩ {v | E v = E u}
  have hT : IsCompact T := hS.inter_right (isClosed_eq hE continuous_const)
  have hsq : Continuous (fun v : Fin n → ℝ ↦ ∑ i, (v i) ^ 2) :=
    continuous_finsetSum _ fun i _ ↦ (continuous_apply i).pow 2
  obtain ⟨v, hv, hvmin⟩ := hT.exists_isMinOn ⟨u, hu, rfl⟩ hsq.continuousOn
  have hconst (a b : Fin n) : v a = v b := by
    by_contra hne
    have hab : a ≠ b := fun h ↦ hne (congrArg v h)
    obtain ⟨z, hz, hzE, hzsq⟩ := exists_coexposure_smoothing hv.1 hab hne j
    have hzT : z ∈ T := ⟨hz, (humax hz).antisymm (hv.2 ▸ hzE)⟩
    exact (not_lt_of_ge (hvmin hzT)) hzsq
  let a : Fin n := ⟨0, hn⟩
  have hvc : ∑ i : Fin n, v i = (n : ℝ) * v a := by
    calc
      _ = ∑ _i : Fin n, v a := sum_congr rfl fun i _ ↦ hconst i a
      _ = _ := by simp
  have hva : v a = 1 / (n : ℝ) := by
    apply (eq_div_iff (by positivity : (n : ℝ) ≠ 0)).mpr
    rw [mul_comm, ← hvc]
    exact hv.1.2
  have hveq (i : Fin n) : v i = 1 / (n : ℝ) := (hconst i a).trans hva
  calc
    E w ≤ E u := humax hwS
    _ = E v := hv.2.symm
    _ = coexposureEsymm univ j (fun _ ↦ 1 / (n : ℝ)) :=
      coexposureEsymm_congr j fun i _ ↦ hveq i
    _ = _ := by
      calc
        coexposureEsymm univ j (fun _ : Fin n ↦ 1 / (n : ℝ)) =
            ∑ _t ∈ (univ : Finset (Fin n)).powersetCard j, (1 / (n : ℝ)) ^ j :=
          sum_congr rfl fun _ ht ↦ by rw [prod_const, (mem_powersetCard.mp ht).2]
        _ = _ := by simp [sum_const, nsmul_eq_mul, card_powersetCard]
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
end StepA2
end

-- ReverseQuadraticGaussian
section
open Finset
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- ReverseCycleCollectionMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- PivotReverseMaskMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- MeasureCountFilterLoss
section
open MeasureTheory
open scoped ENNReal
namespace StepA2
variable {Ω : Type*} [MeasurableSpace Ω]
end StepA2
end

-- ReverseCycleTypeWeightTransfer
section
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- ShortCycleChebyshev
section
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- UniformShortCycleMoments
section
open Equiv Equiv.Perm
open scoped BigOperators
namespace StepA2
variable {α : Type*} [Fintype α] [DecidableEq α]
end StepA2
end

-- PivotReverseFilterMoment
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
private noncomputable def reverseFilterSecondMomentConstant (C : ℝ) : ℝ :=
  2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2)
end StepA2
end

-- PivotScoreLock
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}
end StepA2
end

-- PivotForwardExposureReveal
section
open MeasureTheory Set StableMarriage
namespace StepA2
end StepA2
end

-- PivotEligibilityScale
section
open Filter Real
open scoped BigOperators ENNReal Topology
namespace StepA2
end StepA2
end

-- PivotEligibleRevealControls
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
private def reverseDiagonalMaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).1
namespace ReverseMaskGeometry
variable {n : ℕ} {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
  {μ ρ : Matching n} {s u p : ℝ}
end ReverseMaskGeometry
end StepA2
end

-- PivotSpouseBandMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
private def pivotDiagonalFemaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).2
private def pivotBaseDiagonalBand (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | let X := reverseDiagonalMaleTotal d
       let Y := pivotDiagonalFemaleTotal d
       (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) ∧
       2 ≤ Y ∧ Y ≤ (n : ℝ) ^ (2 / 5 : ℝ) ∧ (n : ℝ) / 128 ≤ X * Y ∧
       (∀ i, (diagonalPairAt d i).2 / Y ≤ 12 * Real.log n / n) ∧
       ∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (Y - 1)}
end StepA2
end

-- CoexposureScoreMomentBound
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
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
end StepA2
end

-- CoexposureScoreRefutation
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
end StepA2
end

-- PivotSpouseBandRegularity
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
private def rankStableSmallFemaleTotalEvent (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
    femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
end StepA2
end

-- PivotSpouseSquareRegularity
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
private def largeSpouseAngularSquareSet (n : ℕ) : Set (Fin n → ℝ) :=
  {w | 24 < pittelAngularSquareScore w}
theorem measurableSet_largeSpouseAngularSquareSet (n : ℕ) :
    MeasurableSet (largeSpouseAngularSquareSet n) := by
  have h : Measurable (pittelAngularSquareScore : (Fin n → ℝ) → ℝ) := by
    unfold pittelAngularSquareScore
    fun_prop
  exact measurableSet_lt measurable_const h
theorem eventually_measure_spouseAngularSquare_gt_le (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop, spouseAngularLaw n (largeSpouseAngularSquareSet n) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_measure_iidExponential_angleSquare_gt_le p hp] with n hn h
  rw [← map_spouseAngle_pi_expMeasure_one hn,
    Measure.map_apply (measurable_spouseAngle n) (measurableSet_largeSpouseAngularSquareSet n)]
  exact h
private def badFemaleSpouseSquareMark {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ spouseAngle (femaleSpouseByHusband μ x) ∈
    largeSpouseAngularSquareSet n}
private theorem size_mul_neg_rpow_shift {n : ℕ} (hn : 0 < n) (p : ℝ) :
    (n : ℝ) * (n : ℝ) ^ (-(p + 1)) = (n : ℝ) ^ (-p) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(p + 1)) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hn', show (1 : ℝ) + -(p + 1) = -p by ring]
private theorem cube_mul_neg_rpow_shift {n : ℕ} (hn : 0 < n) (p : ℝ) :
    (n : ℝ) ^ (3 : ℕ) * (n : ℝ) ^ (-(p + 4)) = (n : ℝ) ^ (-(p + 1)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    _ = (n : ℝ) ^ (3 : ℝ) * (n : ℝ) ^ (-(p + 4)) := by rw [Real.rpow_ofNat]
    _ = _ := by rw [← Real.rpow_add hn', show (3 : ℝ) + -(p + 4) = -(p + 1) by ring]
theorem eventually_sum_measure_badFemaleSpouseSquareMark_le (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n (badFemaleSpouseSquareMark μ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  have hL : ∀ᶠ n : ℕ in atTop, 2 ≤ (9 / 10 : ℝ) * Real.log n :=
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (20 / 9)).mono fun n h ↦ by
        change (20 / 9 : ℝ) ≤ Real.log (n : ℝ) at h
        linarith only [h]
  have hC : ∀ᶠ n : ℕ in atTop, Real.exp 2 ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  filter_upwards [eventually_measure_spouseAngularSquare_gt_le (p + 4) (by positivity),
    eventually_sum_stable_smallSpouseTotalLog_le (p + 1), hL, hC,
    eventually_ge_atTop (2 : ℕ)] with n hangle hsmall hnlog hnC hn
  let E (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
  let B (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
      spouseAngle (femaleSpouseByHusband μ x) ∈ largeSpouseAngularSquareSet n}
  have hn' : 0 < n := by omega
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn'
  have hn₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog₀ : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hlog : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos hn₀).trans (by linarith)
  have hcoef : Real.exp 2 * (n : ℝ) * Real.log n ≤ (n : ℝ) ^ (3 : ℕ) := by
    calc
      _ ≤ (n : ℝ) * n * Real.log n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnC hn₀.le) hlog₀
      _ ≤ (n : ℝ) * n * n := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  let a := (n : ℝ) ^ (-(p + 1))
  have ha : 0 ≤ a := Real.rpow_nonneg hn₀.le _
  have hbulk : (∑ μ : Matching n, continuousScoreLaw n (B μ)) ≤ ENNReal.ofReal a := by
    refine (sum_measure_scoreStable_and_femaleSpouseAngle_le hn
      (measurableSet_largeSpouseAngularSquareSet n)).trans ?_
    calc
      _ ≤ ENNReal.ofReal ((n : ℝ) ^ (3 : ℕ)) * ENNReal.ofReal ((n : ℝ) ^ (-(p + 4))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) hangle
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), cube_mul_neg_rpow_shift hn' p]
  have hcover (μ : Matching n) : badFemaleSpouseSquareMark μ ⊆ E μ ∪ B μ := by
    intro x hx
    by_cases hY : 2 ≤ femaleSpouseTotal x μ
    · exact Or.inr ⟨hx.1, hY, hx.2⟩
    · exact Or.inl ⟨hx.1, (lt_of_not_ge hY).trans_le hnlog⟩
  calc
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n (E μ) + continuousScoreLaw n (B μ)) :=
      Finset.sum_le_sum fun μ _ ↦ (measure_mono (hcover μ)).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal a := by
      rw [Finset.sum_add_distrib]
      exact add_le_add hsmall hbulk
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add ha ha]
      apply ENNReal.ofReal_le_ofReal
      exact (two_mul a).symm.le.trans
        ((mul_le_mul_of_nonneg_right hn₂ ha).trans_eq (size_mul_neg_rpow_shift hn' p))
end StepA2
end

-- ForestDeterministic
section
open scoped BigOperators Classical
namespace StepA2
private def RealizesDirectedCycle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) (σ : Equiv.Perm ι) : Prop :=
  σ.IsCycle ∧ ∀ i ∈ σ.support, f i = some (σ i)
private def IsAcyclicSuccessor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) : Prop :=
  ∀ σ : Equiv.Perm ι, ¬ RealizesDirectedCycle f σ
private noncomputable def successorAdjacency {ι : Type*} [DecidableEq ι]
    (f : ι → Option ι) : Matrix ι ι ℝ :=
  fun i j ↦ if f i = some j then 1 else 0
private theorem det_one_sub_successorAdjacency_eq_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] {f : ι → Option ι} {σ : Equiv.Perm ι}
    (h : RealizesDirectedCycle f σ) : (1 - successorAdjacency f).det = 0 := by
  refine Matrix.det_eq_zero_of_not_linearIndependent_rows fun hlin ↦ ?_
  obtain ⟨i, hi⟩ := h.1.nonempty_support
  have hsum (j : ι) : (∑ k ∈ σ.support, (1 - successorAdjacency f) k j) = 0 :=
    calc
      _ = ∑ k ∈ σ.support, ((if k = j then (1 : ℝ) else 0) - (if σ k = j then 1 else 0)) :=
        Finset.sum_congr rfl fun k hk ↦ by
          simp [Matrix.sub_apply, Matrix.one_apply, successorAdjacency, h.2 k hk]
      _ = 0 := by
        rw [Finset.sum_sub_distrib, sub_eq_zero]
        exact (Finset.sum_equiv σ (fun k ↦ Equiv.Perm.apply_mem_support.symm)
          (fun _ _ ↦ rfl)).symm
  have hcomb : (∑ k ∈ σ.support, (1 : ℝ) • (1 - successorAdjacency f) k) = 0 :=
    funext fun j ↦ by
      simp only [one_smul, Pi.zero_apply]
      exact (Finset.sum_apply j σ.support (fun k ↦ (1 - successorAdjacency f) k)).trans (hsum j)
  exact one_ne_zero ((linearIndependent_iff'.mp hlin) σ.support (fun _ ↦ 1) hcomb i hi)
private theorem det_one_sub_successorAdjacency_eq_one {ι : Type*}
    [Fintype ι] [DecidableEq ι] {f : ι → Option ι}
    (hf : ∀ i, f i ≠ some i) (h : IsAcyclicSuccessor f) :
    (1 - successorAdjacency f).det = 1 := by
  classical
  let A := 1 - successorAdjacency f
  have hprod (σ : Equiv.Perm ι) (hne : σ ≠ 1) : (∏ i, A i (σ i)) = 0 := by
    obtain ⟨τ, hτ⟩ := Finset.nonempty_iff_ne_empty.mpr
      (fun he ↦ hne (Equiv.Perm.cycleFactorsFinset_eq_empty_iff.mp he))
    obtain ⟨hcyc, heq⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hτ
    have hbad : ¬ ∀ i ∈ τ.support, f i = some (τ i) :=
      fun ha ↦ h τ ⟨hcyc, ha⟩
    obtain ⟨i, hi, hfi⟩ := (not_forall.mp hbad).imp fun _ ↦ Classical.not_imp.mp
    have hit : i ≠ τ i := (Equiv.Perm.mem_support.mp hi).symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      simp [A, Matrix.sub_apply, successorAdjacency, hit, ← heq i hi, hfi])
  calc
    A.det = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A i (σ i) := by
      simpa only [Matrix.transpose_apply] using
        (Matrix.det_transpose A).symm.trans (Matrix.det_apply A.transpose)
    _ = Equiv.Perm.sign (1 : Equiv.Perm ι) • ∏ i, A i i := by
      simpa only [Equiv.Perm.one_apply] using
        (Finset.sum_eq_single (1 : Equiv.Perm ι)
          (fun σ _ hne ↦ by rw [hprod σ hne, smul_zero])
          (fun hn ↦ (hn (Finset.mem_univ _)).elim) :
          (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A i (σ i)) = _)
    _ = 1 := by simp [A, Matrix.sub_apply, successorAdjacency, hf]
theorem det_one_sub_successorAdjacency {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) (hf : ∀ i, f i ≠ some i) :
    (1 - successorAdjacency f).det = if IsAcyclicSuccessor f then 1 else 0 := by
  classical
  by_cases h : IsAcyclicSuccessor f
  · simpa only [if_pos h] using det_one_sub_successorAdjacency_eq_one hf h
  · obtain ⟨σ, hσ⟩ := not_forall.mp h
    simpa only [if_neg h] using det_one_sub_successorAdjacency_eq_zero (not_not.mp hσ)
end StepA2
end

-- ForestProductProbability
section
open scoped BigOperators Classical
namespace StepA2
theorem sum_prod_mul_det_eq_det_rowSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (w : ∀ i, κ i → ℝ)
    (a : ∀ i, κ i → ι → ℝ) :
    (∑ x : ∀ i, κ i, (∏ i, w i (x i)) * (Matrix.of (fun i j ↦ a i (x i) j)).det) =
      (Matrix.of (fun i j ↦ ∑ k, w i k * a i k j)).det := by
  let sign (σ : Equiv.Perm ι) : ℝ := ((Equiv.Perm.sign σ : ℤ) : ℝ)
  calc
    _ = ∑ x : ∀ i, κ i, ∑ σ : Equiv.Perm ι,
        sign σ * ∏ i, w i (x i) * a i (x i) (σ i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.prod_mul_distrib]
      simp only [Matrix.transpose_apply, Matrix.of_apply, sign]
      ac_rfl
    _ = ∑ σ : Equiv.Perm ι, sign σ * ∏ i, ∑ k, w i k * a i k (σ i) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      exact congrArg (sign σ * ·) (Fintype.prod_sum (fun i k ↦ w i k * a i k (σ i))).symm
    _ = _ := by
      rw [← Matrix.det_transpose, Matrix.det_apply']
      rfl
theorem sum_prod_mul_det_one_sub_successorAdjacency {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Option ι → ℝ) (hw : ∀ i, ∑ o, w i o = 1) :
    (∑ f : ι → Option ι, (∏ i, w i (f i)) * (1 - successorAdjacency f).det) =
      (1 - Matrix.of (fun i j ↦ w i (some j))).det := by
  let a (i : ι) (o : Option ι) (j : ι) : ℝ :=
    (1 : Matrix ι ι ℝ) i j - (if o = some j then 1 else 0)
  have hmatrix (f : ι → Option ι) :
      Matrix.of (fun i j ↦ a i (f i) j) = 1 - successorAdjacency f := by
    ext i j
    rfl
  have hmean :
      Matrix.of (fun i j ↦ ∑ o, w i o * a i o j) =
        1 - Matrix.of (fun i j ↦ w i (some j)) := by
    ext i j
    simp only [a, Matrix.sub_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hw i, one_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  simpa only [hmatrix, hmean] using sum_prod_mul_det_eq_det_rowSum w a
private noncomputable def forestProductMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Option ι → ℝ) : ℝ :=
  ∑ f : ι → Option ι, (∏ i, w i (f i)) * (if IsAcyclicSuccessor f then 1 else 0)
theorem forestProductMass_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Option ι → ℝ) (hw : ∀ i, ∑ o, w i o = 1)
    (hloop : ∀ i, w i (some i) = 0) :
    forestProductMass w = (1 - Matrix.of (fun i j ↦ w i (some j))).det := by
  unfold forestProductMass
  calc
    _ = ∑ f : ι → Option ι, (∏ i, w i (f i)) * (1 - successorAdjacency f).det := by
      apply Finset.sum_congr rfl
      intro f _
      by_cases hf : ∀ i, f i ≠ some i
      · rw [det_one_sub_successorAdjacency f hf]
      · push Not at hf
        obtain ⟨i, hi⟩ := hf
        have hz : ∏ i, w i (f i) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, hloop])
        simp only [hz, zero_mul]
    _ = _ := sum_prod_mul_det_one_sub_successorAdjacency w hw
end StepA2
end

-- ForestRankOne
section
namespace StepA2
private def rankOneOffDiagonal {ι : Type*} [DecidableEq ι] (q p : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ if i = j then 0 else q i * p j
theorem det_one_sub_rankOneOffDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q p : ι → ℝ) (hu : ∀ i, 0 ≤ q i * p i) :
    (1 - rankOneOffDiagonal q p).det =
      (∏ i, (1 + q i * p i)) * (1 - ∑ i, q i * p i / (1 + q i * p i)) := by
  let v : ι → ℝ := fun i ↦ -(q i / (1 + q i * p i))
  have hd (i : ι) : 1 + q i * p i ≠ 0 := ne_of_gt (by linarith only [hu i])
  have hfactor : 1 - rankOneOffDiagonal q p =
      Matrix.diagonal (fun i ↦ 1 + q i * p i) *
        (1 + Matrix.replicateCol Unit v * Matrix.replicateRow Unit p) := by
    ext i j
    rw [Matrix.diagonal_mul, ← Matrix.vecMulVec_eq Unit]
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
      rankOneOffDiagonal, v]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, sub_zero]
      field_simp [hd i]
      ring
    · simp only [if_neg hij, zero_sub, zero_add]
      field_simp [hd i]
  rw [hfactor, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : p ⬝ᵥ v = -(∑ i, q i * p i / (1 + q i * p i)) := by
    rw [dotProduct, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [v]
    simp only [mul_neg, ← mul_div_assoc, mul_comm (p i) (q i)]
  rw [hdot, sub_eq_add_neg]
theorem det_one_sub_rankOneOffDiagonal_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q p : ι → ℝ) (hu : ∀ i, 0 ≤ q i * p i) (hsum : ∑ i, q i * p i ≤ 1) :
    (1 - rankOneOffDiagonal q p).det ≤
      Real.exp 1 * ((1 - ∑ i, q i * p i) + ∑ i, (q i * p i) ^ 2) := by
  rw [det_one_sub_rankOneOffDiagonal q p hu]
  let u : ι → ℝ := fun i ↦ q i * p i
  change (∏ i, (1 + u i)) * (1 - ∑ i, u i / (1 + u i)) ≤
    Real.exp 1 * ((1 - ∑ i, u i) + ∑ i, (u i) ^ 2)
  have hu' (i : ι) : 0 ≤ u i := hu i
  have hfrac (i : ι) : u i - (u i) ^ 2 ≤ u i / (1 + u i) := by
    apply (le_div_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one (hu' i))).2
    nlinarith only [mul_nonneg (sq_nonneg (u i)) (hu' i)]
  have hbracket : 1 - ∑ i, u i / (1 + u i) ≤ (1 - ∑ i, u i) + ∑ i, (u i) ^ 2 := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hfrac i)
    rw [Finset.sum_sub_distrib] at h
    linarith only [h]
  have hprod : ∏ i, (1 + u i) ≤ Real.exp 1 := by
    calc
      ∏ i, (1 + u i) ≤ ∏ i, Real.exp (u i) :=
        Finset.prod_le_prod (fun i _ ↦ add_nonneg zero_le_one (hu' i))
          (fun i _ ↦ by simpa only [add_comm] using Real.add_one_le_exp (u i))
      _ = Real.exp (∑ i, u i) := (Real.exp_sum Finset.univ u).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsum
  exact (mul_le_mul_of_nonneg_left hbracket
    (Finset.prod_nonneg (fun i _ ↦ add_nonneg zero_le_one (hu' i)))).trans
      (mul_le_mul_of_nonneg_right hprod
        (add_nonneg (sub_nonneg.mpr hsum) (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (u i)))))
end StepA2
end

-- ForestRowThinning
section
open scoped BigOperators Classical
namespace StepA2
private noncomputable def thinningWeight {ι : Type*} [DecidableEq ι]
    (w v : Option ι → ℝ) : Option ι → Option ι → ℝ
  | none, none => w none
  | none, some _ => 0
  | some i, none => w (some i) - v (some i)
  | some i, some j => if i = j then v (some j) else 0
private theorem thinningWeight_nonneg {ι : Type*} [DecidableEq ι]
    {w v : Option ι → ℝ} (hw : ∀ a, 0 ≤ w a) (hv : ∀ a, 0 ≤ v a)
    (hle : ∀ i, v (some i) ≤ w (some i)) (a b : Option ι) :
    0 ≤ thinningWeight w v a b := by
  cases a <;> cases b <;> simp [thinningWeight, hw, sub_nonneg.mpr, hle]
  split <;> simp [hv]
private theorem sum_thinningWeight_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : Option ι → ℝ) (a : Option ι) :
    (∑ b, thinningWeight w v a b) = w a := by
  rw [Fintype.sum_option]
  cases a <;> simp [thinningWeight]
private theorem sum_thinningWeight_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w v : Option ι → ℝ} (hw : ∑ a, w a = 1) (hv : ∑ a, v a = 1) (b : Option ι) :
    (∑ a, thinningWeight w v a b) = v b := by
  rw [Fintype.sum_option] at hw hv ⊢
  cases b with
  | none =>
    simp only [thinningWeight, Finset.sum_sub_distrib]
    rw [← add_sub_assoc, hw, ← hv, add_sub_cancel_right]
  | some j =>
    simp [thinningWeight, eq_comm]
private theorem thinningWeight_ne_zero_of_arc {ι : Type*} [DecidableEq ι]
    {w v : Option ι → ℝ} {a : Option ι} {j : ι}
    (h : thinningWeight w v a (some j) ≠ 0) : a = some j := by
  cases a with
  | none => simp [thinningWeight] at h
  | some k =>
    by_contra hk
    exact h (if_neg fun hkj ↦ hk (congrArg some hkj))
theorem sum_product_le_of_arc_thinning {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : ι → Option ι → ℝ) (hw : ∀ i a, 0 ≤ w i a) (hv : ∀ i a, 0 ≤ v i a)
    (hw1 : ∀ i, ∑ a, w i a = 1) (hv1 : ∀ i, ∑ a, v i a = 1)
    (hle : ∀ i j, v i (some j) ≤ w i (some j)) (F : (ι → Option ι) → ℝ)
    (hmono : ∀ f g, (∀ i j, g i = some j → f i = some j) → F f ≤ F g) :
    (∑ f, (∏ i, w i (f i)) * F f) ≤ ∑ g, (∏ i, v i (g i)) * F g := by
  let c (f g : ι → Option ι) := ∏ i, thinningWeight (w i) (v i) (f i) (g i)
  have hc0 (f g : ι → Option ι) : 0 ≤ c f g :=
    Finset.prod_nonneg fun i _ ↦ thinningWeight_nonneg (hw i) (hv i) (hle i) _ _
  have hm1 (f : ι → Option ι) : (∑ g, c f g) = ∏ i, w i (f i) := by
    dsimp [c]
    rw [← Fintype.prod_sum]
    simp only [sum_thinningWeight_right]
  have hm2 (g : ι → Option ι) : (∑ f, c f g) = ∏ i, v i (g i) := by
    dsimp [c]
    rw [← Fintype.prod_sum (fun i (a : Option ι) ↦ thinningWeight (w i) (v i) a (g i))]
    simp only [sum_thinningWeight_left (hw1 _) (hv1 _)]
  have hobs (f g : ι → Option ι) : c f g * F f ≤ c f g * F g := by
    by_cases h : c f g = 0
    · simp [h]
    apply mul_le_mul_of_nonneg_left _ (hc0 f g)
    apply hmono
    intro i j hij
    apply thinningWeight_ne_zero_of_arc
    intro hzero
    apply h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa only [hij] using hzero
  calc
    _ = ∑ f, ∑ g, c f g * F f := by simp_rw [← Finset.sum_mul, hm1]
    _ ≤ ∑ f, ∑ g, c f g * F g :=
      Finset.sum_le_sum fun f _ ↦ Finset.sum_le_sum fun g _ ↦ hobs f g
    _ = _ := by rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, hm2]
theorem isAcyclicSuccessor_of_arc_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : ι → Option ι} (hfg : ∀ i j, g i = some j → f i = some j)
    (hf : IsAcyclicSuccessor f) : IsAcyclicSuccessor g := by
  intro σ hσ
  exact hf σ ⟨hσ.1, fun i hi ↦ hfg i (σ i) (hσ.2 i hi)⟩
theorem forestProductMass_le_of_arc_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : ι → Option ι → ℝ) (hw : ∀ i a, 0 ≤ w i a) (hv : ∀ i a, 0 ≤ v i a)
    (hw1 : ∀ i, ∑ a, w i a = 1) (hv1 : ∀ i, ∑ a, v i a = 1)
    (hle : ∀ i j, v i (some j) ≤ w i (some j)) :
    forestProductMass w ≤ forestProductMass v := by
  unfold forestProductMass
  apply sum_product_le_of_arc_thinning w v hw hv hw1 hv1 hle
  intro f g hfg
  by_cases hf : IsAcyclicSuccessor f
  · simp [hf, isAcyclicSuccessor_of_arc_subset hfg hf]
  · by_cases hg : IsAcyclicSuccessor g <;> simp [hf, hg]
private def eraseSuccessorRows {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Option ι) (i : ι) : Option ι :=
  if i ∈ s then none else f i
private noncomputable def eraseSuccessorWeights {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w : ι → Option ι → ℝ) (i : ι) (a : Option ι) : ℝ :=
  if i ∈ s then (if a = none then 1 else 0) else w i a
theorem eraseSuccessorWeights_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {w : ι → Option ι → ℝ} (hw : ∀ i a, 0 ≤ w i a) (i : ι) (a : Option ι) :
    0 ≤ eraseSuccessorWeights s w i a := by
  by_cases hi : i ∈ s <;> cases a <;> simp [eraseSuccessorWeights, hi, hw]
theorem sum_eraseSuccessorWeights {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι)
    {w : ι → Option ι → ℝ} (hw : ∀ i, ∑ a, w i a = 1) (i : ι) :
    (∑ a, eraseSuccessorWeights s w i a) = 1 := by
  by_cases hi : i ∈ s <;> simp [eraseSuccessorWeights, hi, hw]
@[simp] theorem eraseSuccessorWeights_some {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w : ι → Option ι → ℝ) (i j : ι) :
    eraseSuccessorWeights s w i (some j) = if i ∈ s then 0 else w i (some j) := by
  simp [eraseSuccessorWeights]
private def IsSoleDirectedCycle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) (σ : Equiv.Perm ι) : Prop :=
  RealizesDirectedCycle f σ ∧ ∀ τ, RealizesDirectedCycle f τ → τ = σ
private noncomputable def soleDirectedCycleProductMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Option ι → ℝ) (σ : Equiv.Perm ι) : ℝ :=
  ∑ f : ι → Option ι, (∏ i, w i (f i)) * (if IsSoleDirectedCycle f σ then 1 else 0)
theorem IsSoleDirectedCycle.isAcyclicSuccessor_erase {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → Option ι} {σ : Equiv.Perm ι} (h : IsSoleDirectedCycle f σ) :
    IsAcyclicSuccessor (eraseSuccessorRows σ.support f) := by
  intro τ hτ
  have hnot (i : ι) (hi : i ∈ τ.support) : i ∉ σ.support := by
    intro his
    have hArc := hτ.2 i hi
    simp [eraseSuccessorRows, his] at hArc
  have hτf : RealizesDirectedCycle f τ :=
    ⟨hτ.1, fun i hi ↦ by simpa [eraseSuccessorRows, hnot i hi] using hτ.2 i hi⟩
  have hτσ := h.2 τ hτf
  subst τ
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr
    (fun hs ↦ h.1.1.ne_one (Equiv.Perm.support_eq_empty_iff.mp hs))
  exact hnot i hi hi
theorem sum_product_prescribed_rows_erase_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Option ι → ℝ) (s : Finset ι) (a : ι → Option ι)
    (F : (ι → Option ι) → ℝ) :
    (∑ f : ι → Option ι, (∏ i, w i (f i)) *
        (if ∀ i ∈ s, f i = a i then F (eraseSuccessorRows s f) else 0)) =
      (∏ i ∈ s, w i (a i)) * ∑ g : ι → Option ι,
        (∏ i, eraseSuccessorWeights s w i (g i)) * F g := by
  let E : Finset (ι → Option ι) := Finset.univ.filter (fun f ↦ ∀ i ∈ s, f i = a i)
  let G : Finset (ι → Option ι) := Finset.univ.filter (fun g ↦ ∀ i ∈ s, g i = none)
  let restore (g : ι → Option ι) (i : ι) : Option ι := if i ∈ s then a i else g i
  have hE (f : ι → Option ι) : f ∈ E ↔ ∀ i ∈ s, f i = a i := by simp [E]
  have hG (g : ι → Option ι) : g ∈ G ↔ ∀ i ∈ s, g i = none := by simp [G]
  have hprod (g : ι → Option ι) (hg : g ∈ G) :
      (∏ i, eraseSuccessorWeights s w i (g i)) = ∏ i ∈ sᶜ, w i (g i) := by
    rw [← Finset.prod_mul_prod_compl s]
    have hleft : (∏ i ∈ s, eraseSuccessorWeights s w i (g i)) = 1 :=
      Finset.prod_eq_one fun i hi ↦ by simp [eraseSuccessorWeights, hi, (hG g).mp hg i hi]
    rw [hleft, one_mul]
    exact Finset.prod_congr rfl fun i hi ↦ by
      simp [eraseSuccessorWeights, Finset.mem_compl.mp hi]
  have hzero (g : ι → Option ι) (hg : g ∉ G) :
      (∏ i, eraseSuccessorWeights s w i (g i)) = 0 := by
    have hn : ¬ ∀ i ∈ s, g i = none := fun h ↦ hg ((hG g).mpr h)
    push Not at hn
    obtain ⟨i, hi, hgi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [eraseSuccessorWeights, hi, hgi])
  calc
    _ = ∑ f ∈ E, (∏ i, w i (f i)) * F (eraseSuccessorRows s f) := by
      unfold E
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun f _ ↦ by split <;> simp
    _ = ∑ g ∈ G, (∏ i ∈ s, w i (a i)) * ((∏ i ∈ sᶜ, w i (g i)) * F g) := by
      refine Finset.sum_bij' (fun f _ ↦ eraseSuccessorRows s f) (fun g _ ↦ restore g)
        (fun f _ ↦ (hG _).mpr fun i hi ↦ by simp [eraseSuccessorRows, hi])
        (fun g _ ↦ (hE _).mpr fun i hi ↦ by simp [restore, hi]) ?_ ?_ ?_
      · intro f hf
        funext i
        by_cases hi : i ∈ s <;> simp [restore, eraseSuccessorRows, hi, (hE f).mp hf]
      · intro g hg
        funext i
        by_cases hi : i ∈ s <;> simp [restore, eraseSuccessorRows, hi, (hG g).mp hg]
      · intro f hf
        rw [← Finset.prod_mul_prod_compl s, mul_assoc]
        congr 1
        · exact Finset.prod_congr rfl fun i hi ↦ congrArg (w i) ((hE f).mp hf i hi)
        · congr 1
          exact Finset.prod_congr rfl fun i hi ↦ by
            simp [eraseSuccessorRows, Finset.mem_compl.mp hi]
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      unfold G
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : g ∈ G
      · rw [if_pos ((hG g).mp hg), hprod g hg]
      · rw [if_neg (fun h ↦ hg ((hG g).mpr h)), hzero g hg, zero_mul]
theorem soleDirectedCycleProductMass_le_arc_prod_mul_forestProductMass
    {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → Option ι → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (σ : Equiv.Perm ι) :
    soleDirectedCycleProductMass w σ ≤
      (∏ i ∈ σ.support, w i (some (σ i))) *
        forestProductMass (eraseSuccessorWeights σ.support w) := by
  unfold soleDirectedCycleProductMass forestProductMass
  rw [← sum_product_prescribed_rows_erase_eq w σ.support (fun i ↦ some (σ i))
    (fun g ↦ if IsAcyclicSuccessor g then 1 else 0)]
  apply Finset.sum_le_sum
  intro f _
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ ↦ hw i (f i))
  by_cases hf : IsSoleDirectedCycle f σ
  · rw [if_pos hf, if_pos hf.1.2, if_pos hf.isAcyclicSuccessor_erase]
  · rw [if_neg hf]
    split
    · split <;> simp
    · exact le_rfl
end StepA2
end

-- ForwardSuccessorRowLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
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
theorem normalizedStableScoreRowLaw_successor_eq {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1) :
    normalizedStableScoreRowLaw d i (scoreRowSuccessorEvent d i j) =
      ENNReal.ofReal (rowEligibilityProbability (diagonalPairAt d i).1
        (diagonalPairAt d j.val).2 *
        scoreRowMass Finset.univ
          (fun k : {k : {k : Fin n // i ≠ k} // k ≠ j} ↦
            rowEligibilityProbability (diagonalPairAt d i).1 (diagonalPairAt d k.val.val).2)
          0 1) := by
  let x := (diagonalPairAt d i).1
  let y (k : {k : Fin n // i ≠ k}) := (diagonalPairAt d k.val).2
  let a (k : {k : Fin n // i ≠ k}) := rowEligibilityProbability x (y k)
  let m (k : {k : Fin n // i ≠ k}) := rowNonblockingLaw x (y k)
  let E := scoreSuccessorPairEvent x (y j) (fun k : {k // k ≠ j} ↦ y k.val)
  let K := scoreRowKernel Finset.univ (fun k : {k // k ≠ j} ↦ y k.val) x
  let L := scoreRowMass Finset.univ (fun k : {k // k ≠ j} ↦ a k.val) 0 1
  change normalizedStableScoreRowLaw d i (scoreRowSuccessorEvent d i j) =
    ENNReal.ofReal (a j * L)
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
        by
          change (Measure.pi m) univ = _
          simpa only [Set.preimage_univ] using h
      _ = ((m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val)) (univ ×ˢ univ) :=
        by rw [Set.univ_prod_univ]
      _ = _ := by rw [Measure.prod_prod, Measure.pi_univ]
  have hden (k : {k : Fin n // i ≠ k}) : 0 < 1 - x * y k := by
    have h := mul_le_mul_of_nonneg_left (hy k.val).2 hx.1
    change x * y k ≤ x * 1 at h
    linarith only [h, hx.2]
  have hm (k : {k : Fin n // i ≠ k}) : m k univ = ENNReal.ofReal (1 - x * y k) :=
    rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ (hy k.val)
  have ht' : stableScoreRowLaw d i univ = ENNReal.ofReal ((1 - x * y j) * K) := by
    rw [ht]
    simp_rw [hm]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ ↦ (hden k.val).le),
      ← ENNReal.ofReal_mul (hden j).le]
    rfl
  have hK : 0 ≤ K := Finset.prod_nonneg fun k _ ↦ (hden k.val).le
  have heq' : stableScoreRowLaw d i (scoreRowSuccessorEvent d i j) =
      stableScoreRowLaw d i univ * ENNReal.ofReal (a j * L) := by
    rw [heq, ht', ← ENNReal.ofReal_mul (mul_nonneg (hden j).le hK)]
    rw [scoreSuccessorPairEvent_mass ⟨hx.1, hx.2.le⟩ (hy j.val)
      (fun k : {k // k ≠ j} ↦ hy k.val.val)]
    congr 1
    rw [scoreRowMass_affine_eq hx (fun k _ ↦ hy k.val.val)]
    change y j * ((1 - x) * K * L) = (1 - x * y j) * K * (a j * L)
    unfold a rowEligibilityProbability
    have hden' : 1 - y j * x ≠ 0 := by simpa only [mul_comm] using (hden j).ne'
    field_simp [(hden j).ne', hden']
  rw [normalizedStableScoreRowLaw, Measure.smul_apply, smul_eq_mul, heq', ← mul_assoc,
    ENNReal.inv_mul_cancel (stableScoreRowLaw_univ_ne_zero d i hx hy) (measure_ne_top _ _),
    one_mul]
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
end StepA2
end

-- ForwardSuccessorOutcome
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
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
theorem forwardSuccessorOutcomeLaw_isProbabilityMeasure {n : ℕ}
    [MeasurableSpace (Option (Fin n))] (d : DiagonalScorePairs n) (i : Fin n)
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1) (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1) :
    IsProbabilityMeasure (forwardSuccessorOutcomeLaw d i) := by
  have := normalizedStableScoreRowLaw_isProbabilityMeasure d i hx hy
  unfold forwardSuccessorOutcomeLaw
  exact Measure.isProbabilityMeasure_map (measurable_forwardSuccessorOutcome d i).aemeasurable
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
theorem map_forwardSuccessorOutcome_pi {n : ℕ} [MeasurableSpace (Option (Fin n))]
    (d : DiagonalScorePairs n) (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) :
    (Measure.pi (normalizedStableScoreRowLaw d)).map
      (fun r i ↦ forwardSuccessorOutcome d i (r i)) =
      Measure.pi (forwardSuccessorOutcomeLaw d) := by
  have (i : Fin n) := normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
  exact Measure.pi_map_pi fun i ↦ (measurable_forwardSuccessorOutcome d i).aemeasurable
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
end StepA2
end

-- PivotForwardRowDeficit
section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
private theorem sum_embedding_le_sum {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) {f : β → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (∑ i, f (e i)) ≤ ∑ i, f i := by
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ ↦ hf i
private theorem rowEligibilityProbability_le_scaled {x y M : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hM : M < 1)
    (hxy : x * y ≤ M) :
    rowEligibilityProbability x y ≤ ((1 - x) / (1 - M)) * y := by
  unfold rowEligibilityProbability
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1)
    (sub_pos.mpr hM) (sub_le_sub_left hxy 1)
theorem forwardSuccessorIntegral_ge {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ↪ ι) (j : ι) {x : ℝ} {y : ι → ℝ} {M P : ℝ}
    (hx : x ∈ Ico 0 1) (hy : ∀ i, y i ∈ Icc 0 1) (hY : 0 < ∑ i, y i)
    (hM : M ∈ Ico 0 1) (hxy : ∀ i, x * y i ≤ M)
    (hP : 0 < P) (hshare : ∀ i, y i / ∑ k, y k ≤ P) :
    (1 - min 1 (M + P + Real.exp (-((1 - x) * ∑ k, y k)))) * (y j / ∑ k, y k) ≤
      rowEligibilityProbability x (y j) *
        scoreRowMass Finset.univ (fun k ↦ rowEligibilityProbability x (y (e k))) 0 1 := by
  let Y := ∑ k, y k
  let c := (1 - x) / (1 - M)
  let A := c * Y
  let b := min 1 (A * P)
  let z := Real.exp (-((1 - x) * Y))
  let a (k : κ) := rowEligibilityProbability x (y (e k))
  have hc : 0 < c := div_pos (sub_pos.mpr hx.2) (sub_pos.mpr hM.2)
  have hA : 0 < A := mul_pos hc hY
  have hb : 0 < b := lt_min zero_lt_one (mul_pos hA hP)
  have ha (k : κ) : a k ≤ c * y (e k) :=
    rowEligibilityProbability_le_scaled hx (hy _) hM.2 (hxy _)
  have hab (k : κ) : a k ∈ Icc 0 b := by
    refine ⟨rowEligibilityProbability_nonneg hx (hy _), le_min
      (rowEligibilityProbability_le_one hx (hy _)) ((ha k).trans ?_)⟩
    have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hY).mp (hshare (e k))) hc.le
    change c * y (e k) ≤ c * (P * Y) at h
    simpa only [A, mul_assoc, mul_comm P Y] using h
  have hsum : ∑ k, a k ≤ A := calc
    _ ≤ ∑ k, c * y (e k) := Finset.sum_le_sum fun k _ ↦ ha k
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_embedding_le_sum e fun i ↦ (hy i).1) hc.le
  have hU : (1 - x) * Y ≤ A := by
    apply mul_le_mul_of_nonneg_right _ hY.le
    exact (le_div_iff₀ (sub_pos.mpr hM.2)).mpr
      (mul_le_of_le_one_right (sub_nonneg.mpr hx.2.le) (by linarith only [hM.1]))
  have hzero : 0 ≤ 1 - z := sub_nonneg.mpr <| Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg (sub_nonneg.mpr hx.2.le) hY.le))
  have hK : (1 - z) / (A * (1 + P)) ≤ scoreRowMass Finset.univ a 0 1 := calc
    _ ≤ (1 - Real.exp (-A)) / (A + b) := by
      have hz : 1 - z ≤ 1 - Real.exp (-A) := sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hU)) 1
      apply div_le_div₀ (hzero.trans hz) hz (add_pos hA hb)
      linarith only [show b ≤ A * P from min_le_right _ _]
    _ ≤ _ := scoreRowMass_lower_bounded hb (min_le_left _ _) (fun k _ ↦ hab k) hA hsum
  have htarget := mul_le_mul (mul_le_rowEligibilityProbability hx (hy j)) hK
    (div_nonneg hzero (by positivity)) (rowEligibilityProbability_nonneg hx (hy j))
  change (1 - min 1 (M + P + z)) * (y j / Y) ≤ _
  refine le_trans ?_ htarget
  have heq : (1 - M) * (1 - z) / (1 + P) * (y j / Y) =
      ((1 - x) * y j) * ((1 - z) / (A * (1 + P))) := by
    dsimp only [A, c]
    field_simp [hY.ne', (sub_pos.mpr hx.2).ne', (sub_pos.mpr hM.2).ne']
  rw [← heq]
  apply mul_le_mul_of_nonneg_right _ (div_nonneg (hy j).1 hY.le)
  by_cases hd : M + P + z ≤ 1
  · rw [min_eq_right hd, le_div_iff₀ (by positivity : 0 < 1 + P)]
    have hz : 0 ≤ z := Real.exp_nonneg _
    nlinarith only [mul_nonneg hM.1 hz, mul_nonneg hP.le (add_nonneg (add_nonneg hM.1 hP.le) hz)]
  · rw [min_eq_left (le_of_not_ge hd), sub_self]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hM.2.le) hzero) (by positivity)
private noncomputable def forwardSpouseWeight {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).2 / ∑ j, (diagonalPairAt d j).2
private noncomputable def forwardReferenceRowDeficit {n : ℕ} (d : DiagonalScorePairs n)
    (M P : ℝ) (i : Fin n) : ℝ :=
  min 1 (M + P + Real.exp (-((1 - (diagonalPairAt d i).1) * pivotDiagonalFemaleTotal d)))
theorem normalizedStableScoreRowLaw_successor_ge_reference {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) {M P : ℝ}
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1) (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1)
    (hY : 0 < ∑ k, (diagonalPairAt d k).2) (hM : M ∈ Ico 0 1)
    (hxy : ∀ k, (diagonalPairAt d i).1 * (diagonalPairAt d k).2 ≤ M)
    (hP : 0 < P) (hshare : ∀ k, forwardSpouseWeight d k ≤ P) :
    ENNReal.ofReal ((1 - forwardReferenceRowDeficit d M P i) * forwardSpouseWeight d j.val) ≤
      normalizedStableScoreRowLaw d i (scoreRowSuccessorEvent d i j) := by
  let e : {k : {k : Fin n // i ≠ k} // k ≠ j} ↪ Fin n :=
    ⟨fun k ↦ k.val.val, fun _ _ h ↦ Subtype.ext (Subtype.ext h)⟩
  rw [normalizedStableScoreRowLaw_successor_eq d i j hx hy]
  exact ENNReal.ofReal_le_ofReal (forwardSuccessorIntegral_ge e j.val hx hy hY hM hxy hP hshare)
private def HasForwardReferenceDeficit {n : ℕ} (d : DiagonalScorePairs n) (budget : ℝ) : Prop :=
  ∃ δ : Fin n → ℝ, (∀ i, δ i ∈ Icc 0 1) ∧
    (∑ i, forwardSpouseWeight d i * δ i) ≤ budget ∧
    ∀ (i : Fin n) (j : {j : Fin n // i ≠ j}),
      ENNReal.ofReal ((1 - δ i) * forwardSpouseWeight d j.val) ≤
        normalizedStableScoreRowLaw d i (scoreRowSuccessorEvent d i j)
theorem referenceForestError_le {ι : Type*} [Fintype ι] {p δ : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (htotal : ∑ i, p i = 1) (hδ : ∀ i, δ i ∈ Icc 0 1) :
    let u (i : ι) := (1 - δ i) * p i
    1 - (∑ i, u i) + (∑ i, u i ^ 2) ≤ (∑ i, p i * δ i) + (∑ i, p i ^ 2) := by
  dsimp only
  have hdef : 1 - (∑ i, (1 - δ i) * p i) = ∑ i, p i * δ i := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, htotal, sub_sub_cancel,
      mul_comm (δ _) (p _)]
  rw [hdef]
  refine add_le_add le_rfl ?_
  apply Finset.sum_le_sum
  intro i _
  apply pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr (hδ i).2) (hp i)) _ 2
  exact mul_le_of_le_one_left (hp i) (by linarith only [(hδ i).1])
private theorem eventually_forwardReferenceScales :
    ∀ᶠ n : ℕ in atTop, 1 < n ∧
      192 * Real.log (n : ℝ) ^ 2 / n ≤ (n : ℝ) ^ (-3 / 4 : ℝ) ∧
      12 * Real.log n / n ≤ (n : ℝ) ^ (-3 / 4 : ℝ) := by
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hbound := (((isLittleO_log_rpow_rpow_atTop (s := (1 / 4 : ℝ)) 2
    (by norm_num)).const_mul_left 192).comp_tendsto hcast).eventuallyLE
  filter_upwards [eventually_gt_atTop (1 : ℕ),
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1, hbound] with n hn hlog hbound
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  change |192 * Real.log (n : ℝ) ^ (2 : ℝ)| ≤ |(n : ℝ) ^ (1 / 4 : ℝ)| at hbound
  rw [Real.rpow_two, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hbound
  change 1 ≤ Real.log (n : ℝ) at hlog
  rw [show (-3 / 4 : ℝ) = 1 / 4 - 1 by norm_num, Real.rpow_sub_one hn₀.ne']
  exact ⟨hn, div_le_div_of_nonneg_right hbound hn₀.le,
    div_le_div_of_nonneg_right (le_trans (by nlinarith [sq_nonneg (Real.log n - 1)]) hbound) hn₀.le⟩
theorem eventually_hasForwardReferenceDeficit :
    ∀ᶠ n : ℕ in atTop, ∀ d : DiagonalScorePairs n,
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      2 ≤ pivotDiagonalFemaleTotal d →
      (∀ i, forwardSpouseWeight d i ≤ 12 * Real.log n / n) →
      (∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (pivotDiagonalFemaleTotal d - 1)) →
      (∑ i, forwardSpouseWeight d i *
        Real.exp (-((1 - (diagonalPairAt d i).1) * pivotDiagonalFemaleTotal d))) ≤
        (n : ℝ) ^ (-3 / 4 : ℝ) →
      HasForwardReferenceDeficit d (3 * (n : ℝ) ^ (-3 / 4 : ℝ)) := by
  filter_upwards [eventually_forwardReferenceScales] with n ⟨hn, hMbound, hPbound⟩
  intro d hx hy hY hweight hmale hend
  let Y := pivotDiagonalFemaleTotal d
  let T : ℝ := (n : ℝ) ^ (-3 / 4 : ℝ)
  let M : ℝ := 192 * Real.log (n : ℝ) ^ 2 / n
  let P : ℝ := 12 * Real.log n / n
  have hn₁ : 1 < (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith only [hn₁]
  have hlog₀ := (Real.log_pos hn₁).le
  have hY' : 2 ≤ Y := hY
  have hY₀ : 0 < Y := by linarith only [hY']
  have hT : T < 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt hn₁
      (show (-3 / 4 : ℝ) < 0 by norm_num)
  have hM : M ∈ Ico 0 1 := ⟨by unfold M; positivity, hMbound.trans_lt hT⟩
  have hP : 0 < P := div_pos (mul_pos (by norm_num) (Real.log_pos hn₁)) hn₀
  have hweight₀ (i : Fin n) : 0 ≤ forwardSpouseWeight d i := div_nonneg (hy i).1 hY₀.le
  have hweights : ∑ i, forwardSpouseWeight d i = 1 := by
    unfold forwardSpouseWeight
    rw [← Finset.sum_div]
    change Y / Y = 1
    exact div_self hY₀.ne'
  have hyraw (j : Fin n) :
      (diagonalPairAt d j).2 = Y * forwardSpouseWeight d j := by
    unfold forwardSpouseWeight
    change (diagonalPairAt d j).2 = Y * ((diagonalPairAt d j).2 / Y)
    field_simp [hY₀.ne']
  have hprod (i j : Fin n) : (diagonalPairAt d i).1 * (diagonalPairAt d j).2 ≤ M := by
    have hrat : Y / (Y - 1) ≤ 2 :=
      (div_le_iff₀ (by linarith only [hY'])).mpr (by linarith only [hY'])
    calc
      _ ≤ (8 * Real.log n / (Y - 1)) * (diagonalPairAt d j).2 :=
        mul_le_mul_of_nonneg_right (hmale i) (hy j).1
      _ = (8 * Real.log n * (Y / (Y - 1))) * forwardSpouseWeight d j := by
        rw [hyraw]
        ring
      _ ≤ (16 * Real.log n) * forwardSpouseWeight d j := by
        apply mul_le_mul_of_nonneg_right _ (hweight₀ j)
        linarith only [mul_le_mul_of_nonneg_left hrat (by positivity : 0 ≤ 8 * Real.log (n : ℝ))]
      _ ≤ (16 * Real.log n) * (12 * Real.log n / n) :=
        mul_le_mul_of_nonneg_left (hweight j) (by positivity)
      _ = M := by unfold M; ring
  refine ⟨forwardReferenceRowDeficit d M P, fun i ↦
    ⟨le_min zero_le_one (add_nonneg (add_nonneg hM.1 hP.le) (Real.exp_nonneg _)),
      min_le_left _ _⟩, ?_, fun i j ↦
    normalizedStableScoreRowLaw_successor_ge_reference d i j (hx i) hy hY₀ hM
      (hprod i) hP hweight⟩
  calc
    _ ≤ ∑ i, forwardSpouseWeight d i *
        ((M + P) + Real.exp (-((1 - (diagonalPairAt d i).1) * Y))) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (min_le_right _ _) (hweight₀ i)
    _ = (M + P) + ∑ i, forwardSpouseWeight d i *
        Real.exp (-((1 - (diagonalPairAt d i).1) * Y)) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hweights, one_mul]
    _ ≤ 3 * T := (add_le_add (add_le_add hMbound hPbound) hend).trans_eq (by ring)
end StepA2
end

-- PivotForwardForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
open scoped Classical in
theorem measureReal_pi_eq_sum_event {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (ν : ι → Measure β) [∀ i, IsProbabilityMeasure (ν i)] (E : Set (ι → β)) :
    (Measure.pi ν).real E =
      ∑ f : ι → β, if f ∈ E then ∏ i, (ν i).real {f i} else 0 := by
  let S : Finset (ι → β) := Finset.univ.filter (· ∈ E)
  have hS : (S : Set (ι → β)) = E := by
    ext f
    simp [S]
  have hsingle (f : ι → β) : (Measure.pi ν).real {f} = ∏ i, (ν i).real {f i} := by
    simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  rw [← hS, ← sum_measureReal_singleton S]
  simp_rw [hsingle]
  rw [hS, ← Finset.sum_filter]
private theorem sum_measureReal_singletons_eq_one {β : Type*} [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (ν : Measure β) [IsProbabilityMeasure ν] : ∑ o, ν.real {o} = 1 := by
  rw [sum_measureReal_singleton]
  simp only [Finset.coe_univ, measureReal_def, measure_univ, ENNReal.toReal_one]
open scoped Classical in
private noncomputable def forwardReferenceWeight {ι : Type*} [Fintype ι]
    (p δ : ι → ℝ) (i : ι) : Option ι → ℝ
  | some j => if i = j then 0 else (1 - δ i) * p j
  | none => 1 - ∑ j, if i = j then 0 else (1 - δ i) * p j
theorem sum_forwardReferenceWeight {ι : Type*} [Fintype ι] (p δ : ι → ℝ) (i : ι) :
    (∑ o, forwardReferenceWeight p δ i o) = 1 := by
  rw [Fintype.sum_option]
  simp only [forwardReferenceWeight, sub_add_cancel]
open scoped Classical in
theorem forwardReferenceWeight_nonneg {ι : Type*} [Fintype ι] {p δ : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (ht : ∑ i, p i = 1) (hd : ∀ i, δ i ∈ Icc 0 1)
    (i : ι) (o : Option ι) : 0 ≤ forwardReferenceWeight p δ i o := by
  have harc (j : ι) : 0 ≤ (1 - δ i) * p j :=
    mul_nonneg (sub_nonneg.mpr (hd i).2) (hp j)
  have hfac : 1 - δ i ≤ 1 := sub_le_self _ (hd i).1
  cases o with
  | none =>
    simp only [forwardReferenceWeight]
    apply sub_nonneg.mpr
    refine le_trans (Finset.sum_le_sum fun j _ ↦ ?_) (le_of_eq ht)
    by_cases hij : i = j
    · simpa only [if_pos hij] using hp j
    · simpa only [if_neg hij] using mul_le_of_le_one_left (hp j) hfac
  | some j =>
    by_cases hij : i = j
    · simp only [forwardReferenceWeight, if_pos hij, le_refl]
    · simpa only [forwardReferenceWeight, if_neg hij] using harc j
open scoped Classical in
theorem forestProductMass_forwardReferenceWeight_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) {p δ : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (ht : ∑ i, p i = 1) (hd : ∀ i, δ i ∈ Icc 0 1) :
    forestProductMass (forwardReferenceWeight p (fun i ↦ if i ∈ S then 1 else δ i)) ≤
      Real.exp 1 * ((∑ i, p i * δ i) + (∑ i, p i ^ 2) + ∑ i ∈ S, p i) := by
  let δ' (i : ι) := if i ∈ S then (1 : ℝ) else δ i
  let u (i : ι) := (1 - δ' i) * p i
  have hd' (i : ι) : δ' i ∈ Icc 0 1 := by
    by_cases hi : i ∈ S
    · simp [δ', hi]
    · simpa only [δ', if_neg hi] using hd i
  have hloop (i : ι) : forwardReferenceWeight p δ' i (some i) = 0 := by
    simp [forwardReferenceWeight]
  have hu (i : ι) : 0 ≤ u i := mul_nonneg (sub_nonneg.mpr (hd' i).2) (hp i)
  have hut : ∑ i, u i ≤ 1 :=
    (Finset.sum_le_sum fun i _ ↦ mul_le_of_le_one_left (hp i) (sub_le_self _ (hd' i).1)).trans_eq ht
  rw [forestProductMass_eq_det _ (sum_forwardReferenceWeight p δ') hloop]
  have hM : Matrix.of (fun i j ↦ forwardReferenceWeight p δ' i (some j)) =
      rankOneOffDiagonal (fun i ↦ 1 - δ' i) p := by
    ext i j
    by_cases h : i = j <;> simp [forwardReferenceWeight, rankOneOffDiagonal, h]
  rw [hM]
  refine (det_one_sub_rankOneOffDiagonal_le _ _ hu hut).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  refine (referenceForestError_le hp ht hd').trans ?_
  have hδsum : (∑ i, p i * δ' i) ≤ (∑ i, p i * δ i) + ∑ i ∈ S, p i := by
    calc
      _ ≤ ∑ i, (p i * δ i + if i ∈ S then p i else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ S
        · simpa only [δ', if_pos hi, mul_one] using
            (le_add_of_nonneg_left (mul_nonneg (hp i) (hd i).1))
        · simp only [δ', if_neg hi, add_zero, le_refl]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_filter]; simp
  linarith only [hδsum]
open scoped Classical in
theorem forestProductMass_eraseSuccessorWeights_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (w : ι → Option ι → ℝ) {p δ : ι → ℝ}
    (hw : ∀ i o, 0 ≤ w i o) (hw₁ : ∀ i, ∑ o, w i o = 1)
    (hp : ∀ i, 0 ≤ p i) (ht : ∑ i, p i = 1) (hd : ∀ i, δ i ∈ Icc 0 1)
    (harc : ∀ i j, i ≠ j → (1 - δ i) * p j ≤ w i (some j)) :
    forestProductMass (eraseSuccessorWeights S w) ≤
      Real.exp 1 * ((∑ i, p i * δ i) + (∑ i, p i ^ 2) + ∑ i ∈ S, p i) := by
  let δ' (i : ι) := if i ∈ S then (1 : ℝ) else δ i
  have hd' (i : ι) : δ' i ∈ Icc 0 1 := by
    by_cases hi : i ∈ S
    · simp [δ', hi]
    · simpa only [δ', if_neg hi] using hd i
  refine (forestProductMass_le_of_arc_le (eraseSuccessorWeights S w)
    (forwardReferenceWeight p δ') (eraseSuccessorWeights_nonneg S hw)
    (forwardReferenceWeight_nonneg hp ht hd') (sum_eraseSuccessorWeights S hw₁)
    (sum_forwardReferenceWeight p δ') ?_).trans
      (forestProductMass_forwardReferenceWeight_le S hp ht hd)
  intro i j
  by_cases hi : i ∈ S
  · rw [eraseSuccessorWeights_some, if_pos hi]
    simp [forwardReferenceWeight, δ', hi]
  · rw [eraseSuccessorWeights_some, if_neg hi]
    by_cases hij : i = j
    · simpa [forwardReferenceWeight, hij] using hw i (some j)
    · simpa only [forwardReferenceWeight, if_neg hij, δ', if_neg hi] using harc i j hij
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
theorem prod_forwardOutcomeWeight_le_of_arc_le {n : ℕ} [MeasurableSpace (Option (Fin n))]
    {d : DiagonalScorePairs n} (σ : Matching n) {C : ℝ}
    (harc : ∀ i j, i ≠ j → forwardOutcomeWeight d i (some j) ≤ C * forwardSpouseWeight d j) :
    (∏ i ∈ σ.support, forwardOutcomeWeight d i (some (σ i))) ≤
      C ^ σ.support.card * ∏ i ∈ σ.support, forwardSpouseWeight d i := by
  calc
    _ ≤ ∏ i ∈ σ.support, C * forwardSpouseWeight d (σ i) :=
      Finset.prod_le_prod (fun _ _ ↦ ENNReal.toReal_nonneg)
        (fun i hi ↦ harc i (σ i) (Equiv.Perm.mem_support.mp hi).symm)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      congr 1
      exact Finset.prod_equiv σ (fun i ↦ Equiv.Perm.apply_mem_support.symm) (fun _ _ ↦ rfl)
open scoped Classical in
theorem measureReal_pi_forwardOutcome_eq_sum {n : ℕ} [MeasurableSpace (Option (Fin n))]
    [MeasurableSingletonClass (Option (Fin n))] (d : DiagonalScorePairs n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) (E : Set (Fin n → Option (Fin n))) :
    (Measure.pi (normalizedStableScoreRowLaw d)).real
      ((fun r i ↦ forwardSuccessorOutcome d i (r i)) ⁻¹' E) =
        ∑ f : Fin n → Option (Fin n), if f ∈ E then ∏ i, forwardOutcomeWeight d i (f i) else 0 := by
  have (i : Fin n) := forwardSuccessorOutcomeLaw_isProbabilityMeasure d i (hx i) hy
  have hmeas : Measurable fun r : OffDiagonalScoreRows n ↦
      fun i ↦ forwardSuccessorOutcome d i (r i) :=
    measurable_pi_iff.mpr fun i ↦
      (measurable_forwardSuccessorOutcome d i).comp (measurable_pi_apply i)
  have hE : MeasurableSet E := E.to_countable.measurableSet
  unfold Measure.real
  rw [← Measure.map_apply hmeas hE, map_forwardSuccessorOutcome_pi d hx hy]
  exact measureReal_pi_eq_sum_event (forwardSuccessorOutcomeLaw d) E
open scoped Classical in
theorem measureReal_pi_soleForwardCycle_le {n : ℕ} [MeasurableSpace (Option (Fin n))]
    [MeasurableSingletonClass (Option (Fin n))] (d : DiagonalScorePairs n) (σ : Matching n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1)
    (hY : 0 < ∑ i, (diagonalPairAt d i).2) {b : ℝ}
    (hdef : HasForwardReferenceDeficit d b) :
    (Measure.pi (normalizedStableScoreRowLaw d)).real
      {r | IsSoleDirectedCycle (fun i ↦ forwardSuccessorOutcome d i (r i)) σ} ≤
      (∏ i ∈ σ.support, forwardOutcomeWeight d i (some (σ i))) *
        (Real.exp 1 * (b + (∑ i, (forwardSpouseWeight d i) ^ 2) +
          ∑ i ∈ σ.support, forwardSpouseWeight d i)) := by
  let w := forwardOutcomeWeight d
  let p := forwardSpouseWeight d
  have (i : Fin n) := forwardSuccessorOutcomeLaw_isProbabilityMeasure d i (hx i) hy
  have hw (i : Fin n) (o : Option (Fin n)) : 0 ≤ w i o := ENNReal.toReal_nonneg
  have hw₁ (i : Fin n) : ∑ o, w i o = 1 := sum_measureReal_singletons_eq_one _
  have hp (i : Fin n) : 0 ≤ p i := div_nonneg (hy i).1 hY.le
  have ht : ∑ i, p i = 1 := by
    unfold p forwardSpouseWeight
    rw [← Finset.sum_div, div_self hY.ne']
  obtain ⟨δ, hd, hbudget, harc⟩ := hdef
  have harc' (i j : Fin n) (hij : i ≠ j) : (1 - δ i) * p j ≤ w i (some j) := by
    have := normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
    rw [show w i (some j) = _ from forwardOutcomeWeight_some d i ⟨j, hij⟩]
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (harc i ⟨j, hij⟩)
    rwa [ENNReal.toReal_ofReal (mul_nonneg (sub_nonneg.mpr (hd i).2) (hp j))] at h
  change (Measure.pi (normalizedStableScoreRowLaw d)).real
    ((fun r i ↦ forwardSuccessorOutcome d i (r i)) ⁻¹' {f | IsSoleDirectedCycle f σ}) ≤ _
  rw [measureReal_pi_forwardOutcome_eq_sum d hx hy]
  have heq : (∑ f : Fin n → Option (Fin n), if f ∈ {f | IsSoleDirectedCycle f σ} then
      ∏ i, w i (f i) else 0) = soleDirectedCycleProductMass w σ := by
    unfold soleDirectedCycleProductMass
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : IsSoleDirectedCycle f σ <;> simp [hf]
  change (∑ f : Fin n → Option (Fin n), if f ∈ {f | IsSoleDirectedCycle f σ} then
    ∏ i, w i (f i) else 0) ≤ _
  rw [heq]
  refine (soleDirectedCycleProductMass_le_arc_prod_mul_forestProductMass w hw σ).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ ↦ hw i _)
  refine (forestProductMass_eraseSuccessorWeights_le σ.support w hw hw₁ hp ht hd harc').trans ?_
  exact mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hbudget le_rfl) le_rfl) (Real.exp_pos _).le
private def IsSoleForwardExposedRotation {n : ℕ} (p : Profile n) (μ σ : Matching n) : Prop :=
  IsExposedRotation p μ σ ∧ ∀ τ, IsExposedRotation p μ τ → τ = σ
private def soleForwardExposedRowEvent {n : ℕ} (μ σ : Matching n)
    (d : DiagonalScorePairs n) : Set (OffDiagonalScoreRows n) :=
  {r | IsSoleForwardExposedRotation
    (profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))) μ σ}
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
theorem ae_diagonal_measureReal_soleForwardExposed_le {n : ℕ}
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    (μ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n,
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      0 < (∑ i, (diagonalPairAt d i).2) →
      ∀ (b : ℝ), HasForwardReferenceDeficit d b → ∀ σ : Matching n,
        (Measure.pi (normalizedStableScoreRowLaw d)).real (soleForwardExposedRowEvent μ σ d) ≤
          (∏ i ∈ σ.support, forwardOutcomeWeight d i (some (σ i))) *
            (Real.exp 1 * (b + (∑ i, (forwardSpouseWeight d i) ^ 2) +
              ∑ i ∈ σ.support, forwardSpouseWeight d i)) := by
  filter_upwards [ae_diagonal_ae_normalizedStableRows μ] with d hd
  intro hx hy hY b hdef σ
  have heq : soleForwardExposedRowEvent μ σ d
      =ᵐ[Measure.pi (normalizedStableScoreRowLaw d)]
      {r | IsSoleDirectedCycle (fun i ↦ forwardSuccessorOutcome d i (r i)) σ} := by
    filter_upwards [hd hx hy] with r hr
    have hbridge (τ : Matching n) := realizesDirectedCycle_forwardOutcome_iff μ d r τ hr.2 hr.1
    apply propext
    exact ⟨fun h ↦ ⟨(hbridge σ).mpr h.1, fun τ hτ ↦ h.2 τ ((hbridge τ).mp hτ)⟩,
      fun h ↦ ⟨(hbridge σ).mp h.1, fun τ hτ ↦ h.2 τ ((hbridge τ).mpr hτ)⟩⟩
  have hm := measure_congr heq
  unfold Measure.real
  rw [hm]
  exact measureReal_pi_soleForwardCycle_le d σ hx hy hY hdef
theorem ae_diagonal_measureReal_soleForwardExposed_le_of_goodDiagonalScores {n : ℕ}
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    (μ : Matching n) (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) :
    ∀ᵐ d ∂diagonalScoreLaw n,
      d ∈ goodDiagonalScores n →
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      ∀ (b : ℝ), HasForwardReferenceDeficit d b → ∀ σ : Matching n,
        (Measure.pi (normalizedStableScoreRowLaw d)).real (soleForwardExposedRowEvent μ σ d) ≤
          ((1 + coexposureSuccessorPerturbation n) ^ σ.support.card *
            ∏ i ∈ σ.support, forwardSpouseWeight d i) *
            (Real.exp 1 * (b + (∑ i, (forwardSpouseWeight d i) ^ 2) +
              ∑ i ∈ σ.support, forwardSpouseWeight d i)) := by
  filter_upwards [ae_diagonal_measureReal_soleForwardExposed_le μ] with d hd
  intro hg hx hy b hb σ
  have hY : 0 < ∑ i, (diagonalPairAt d i).2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hg.1
  have hp (i : Fin n) : 0 ≤ forwardSpouseWeight d i := div_nonneg (hy i).1 hY.le
  have hb₀ : 0 ≤ b := by
    obtain ⟨δ, hδ, hsum, _⟩ := hb
    exact (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (hδ i).1).trans hsum
  refine (hd hx hy hY b hb σ).trans ?_
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (Real.exp_pos _).le (add_nonneg
      (add_nonneg hb₀ (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      (Finset.sum_nonneg fun i _ ↦ hp i)))
  exact prod_forwardOutcomeWeight_le_of_arc_le σ fun i j hij ↦
    forwardOutcomeWeight_some_le_of_goodDiagonalScores hg hx hy hA hB hδ i ⟨j, hij⟩
end StepA2
end

-- PivotLocalEligibility
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
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
theorem measurableSet_localPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurableSet {d : DiagonalScorePairs n | LocalPivotGeometry b A B μ ρ d flag} := MarkedLP.measurableSet_localPivotGeometry b A B μ ρ flag

end StepA2
end

-- PivotMarkedDecorationCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
variable {n : ℕ}
section MatchingEndpoints
variable {x : ScoreProfile n} {μ₀ μ ρ σ : Matching n}
  {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ}
end MatchingEndpoints
end StepA2
end

-- PivotRestrictedMoment
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
section ConditionalOrder
variable {Ω : Type*} {m m₀ : MeasurableSpace Ω}
end ConditionalOrder
end StepA2
end

-- PivotFullRevealLaw
section
open MeasureTheory Set StableMarriage
open scoped ENNReal
namespace StepA2
variable {n : ℕ}
end StepA2
end

-- PivotConditionalMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
variable {n : ℕ}
end StepA2
end

-- DeferredAcceptanceTranscript
section
open StableMarriage
open scoped BigOperators
namespace StepA2
namespace DAState
variable {n : ℕ}
end DAState
end StepA2
end

-- UniformStreamRanks
section
open Function MeasureTheory
open scoped ENNReal StepA2
namespace StepA2
variable {n T : ℕ}
end StepA2
end

-- AdaptiveFiniteQueries
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
variable {I A : Type*}
variable [Fintype I] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
end StepA2
end

-- DAStreamSimulation
section
open StableMarriage
namespace StepA2
namespace DAStreamState
variable {n T : ℕ}
end DAStreamState
end StepA2
end

-- DAProposalCoupon
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology StepA2
namespace StepA2
variable {n T : ℕ}
end StepA2
end

-- AdaptiveScoreRectangles
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
variable {ι : Type*}
variable [DecidableEq ι]
variable [Fintype ι]
end StepA2
end

-- UniformLogScoreMoments
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA2
section FiniteProduct
variable {ι : Type*}
variable [Fintype ι]


end FiniteProduct
end StepA2
end

-- AdaptiveScoreFiberMoments
section
open MeasureTheory Set
open scoped BigOperators ENNReal MeasureTheory
namespace StepA2
section Fiber
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
end Fiber
section Cache
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

end Cache
end StepA2
end

-- AdaptiveScoreFiberAssembly
section
open MeasureTheory Set
namespace StepA2
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

end StepA2
end

-- RotationParticipationClock
section
open StableMarriage
open scoped BigOperators
namespace StepA2
end StepA2
end

-- RotationClockCells
section
open StableMarriage
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ ν : Matching n}
variable {ρ : Equiv.Perm (Fin n)}
end StepA2
end

-- RotationSuccessorQueries
section
open StableMarriage
namespace StepA2
variable {n : ℕ}
variable {p : Profile n} {μ : Matching n} {m w : Fin n}
end StepA2
end

-- ScoreRotationWalk
section
open StableMarriage
namespace StepA2
variable {n : ℕ}
end StepA2
end

-- ScoreRotationBranchLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators Classical
namespace StepA2
variable {n : ℕ}
end StepA2
end

-- DALowerEndpoint
section
open Filter MeasureTheory Set StableMarriage
open scoped Classical ENNReal Topology
namespace StepA2
variable {n : ℕ}
end StepA2
end

-- ExponentialSpouseLogTail
section
open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
namespace StepA2
local instance : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)
end StepA2
end

-- MarkedSpouseLogGeometry
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
end StepA2
end

-- CycleSupportCount
section
open Equiv.Perm Finset
open scoped BigOperators Classical
namespace StepA2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem cycleType_ofSubtype_eq_iff {S : Finset ι} (τ : Equiv.Perm S) :
    τ.cycleType = {S.card} ↔ (ofSubtype τ).IsCycle ∧ (ofSubtype τ).support = S := by
  have htype : (ofSubtype τ).cycleType = τ.cycleType :=
    cycleType_extendDomain (α := ↥S) (p := fun i ↦ i ∈ S) (Equiv.refl _) (g := τ)
  rw [← htype]
  constructor
  · intro h
    have hc : (ofSubtype τ).IsCycle := card_cycleType_eq_one.mp (by rw [h]; rfl)
    have hs : (ofSubtype τ).support.card = S.card := by
      rw [← sum_cycleType, h, Multiset.sum_singleton]
    refine ⟨hc, eq_of_subset_of_card_le ?_ hs.ge⟩
    intro i hi
    by_contra hn
    exact (mem_support.mp hi) (ofSubtype_apply_of_not_mem τ hn)
  · rintro ⟨hc, hs⟩
    rw [hc.cycleType, hs]
theorem card_cyclesWithSupport (S : Finset ι) (hS : 2 ≤ S.card) :
    (Finset.univ.filter (fun σ : Equiv.Perm ι ↦ σ.IsCycle ∧ σ.support = S)).card =
      (S.card - 1).factorial := by
  let A := Finset.univ.filter (fun τ : Equiv.Perm S ↦ τ.cycleType = {S.card})
  have hcount : A.card = (S.card - 1).factorial := by
    have hcard : Fintype.card S = S.card := Fintype.card_coe S
    simpa only [A, hcard, Nat.choose_self, mul_one] using
      (card_of_cycleType_singleton (α := S) hS hcard.ge)
  rw [← hcount]
  symm
  refine Finset.card_bij (fun τ _ ↦ ofSubtype τ) ?_ ?_ ?_
  · intro τ hτ
    exact mem_filter.mpr ⟨mem_univ _, (cycleType_ofSubtype_eq_iff τ).mp (mem_filter.mp hτ).2⟩
  · intro τ₁ _ τ₂ _ h
    exact ofSubtype_injective h
  · intro σ hσ
    obtain ⟨hc, hs⟩ := (mem_filter.mp hσ).2
    have hInv := isInvariant_of_support_le (show σ.support ⊆ S from hs.le)
    let τ := σ.subtypePerm hInv
    have heq : ofSubtype τ = σ :=
      (ofSubtype_eq_iff hInv).mpr ⟨hs.le, fun _ ↦ rfl⟩
    refine ⟨τ, mem_filter.mpr ⟨mem_univ _, (cycleType_ofSubtype_eq_iff τ).mpr ?_⟩, heq⟩
    rw [heq]
    exact ⟨hc, hs⟩
theorem sum_cyclesWithLength_by_support (k : ℕ) (hk : 2 ≤ k) (F : Finset ι → ℝ) :
    (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm ι ↦ σ.IsCycle ∧ σ.support.card = k),
      F σ.support) =
      ((k - 1).factorial : ℝ) * ∑ S ∈ (Finset.univ : Finset ι).powersetCard k, F S := by
  let C := Finset.univ.filter (fun σ : Equiv.Perm ι ↦ σ.IsCycle ∧ σ.support.card = k)
  let P := (Finset.univ : Finset ι).powersetCard k
  have hm : ∀ σ ∈ C, σ.support ∈ P := fun σ hσ ↦
    mem_powersetCard.mpr ⟨subset_univ _, (mem_filter.mp hσ).2.2⟩
  change (∑ σ ∈ C, F σ.support) = ((k - 1).factorial : ℝ) * ∑ S ∈ P, F S
  rw [← sum_fiberwise_of_maps_to' hm F, mul_sum]
  refine sum_congr rfl fun S hS ↦ ?_
  have hcard : S.card = k := (mem_powersetCard.mp hS).2
  have hfiber :
      C.filter (fun σ ↦ σ.support = S) =
        Finset.univ.filter (fun σ : Equiv.Perm ι ↦ σ.IsCycle ∧ σ.support = S) := by
    ext σ
    simp only [C, mem_filter, mem_univ, true_and]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2 ▸ hcard⟩, h.2⟩⟩
  rw [hfiber, sum_const, nsmul_eq_mul, card_cyclesWithSupport S (hcard.symm ▸ hk), hcard]
end StepA2
end

-- PointedSymmetricSums
section
open Finset
open scoped BigOperators
namespace StepA2
private theorem sum_supports_containing_eq {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {i : ι} (hi : i ∈ s) (k : ℕ) (p r : ι → ℝ) :
    (∑ S ∈ (s.powersetCard (k + 1)).filter (fun S ↦ i ∈ S),
      (∏ j ∈ S, p j) * r i) =
      ∑ T ∈ (s.erase i).powersetCard k, (p i * r i) * ∏ j ∈ T, p j := by
  refine sum_bij' (fun S _ ↦ S.erase i) (fun T _ ↦ insert i T) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rcases mem_filter.mp hS with ⟨hS, hiS⟩
    rcases mem_powersetCard.mp hS with ⟨hsub, hcard⟩
    exact mem_powersetCard.mpr
      ⟨fun j hj ↦ mem_erase.mpr ⟨(mem_erase.mp hj).1, hsub (mem_erase.mp hj).2⟩,
        by rw [card_erase_of_mem hiS, hcard, Nat.add_sub_cancel]⟩
  · intro T hT
    rcases mem_powersetCard.mp hT with ⟨hsub, hcard⟩
    have hiT : i ∉ T := fun h ↦ notMem_erase i s (hsub h)
    exact mem_filter.mpr
      ⟨mem_powersetCard.mpr
        ⟨insert_subset hi fun _ hj ↦ mem_of_mem_erase (hsub hj),
          by rw [card_insert_of_notMem hiT, hcard]⟩,
        mem_insert_self i T⟩
  · exact fun _ hS ↦ insert_erase (mem_filter.mp hS).2
  · exact fun _ hT ↦ erase_insert (fun h ↦ notMem_erase i s ((mem_powersetCard.mp hT).1 h))
  · intro S hS
    rw [← prod_erase_mul S p (mem_filter.mp hS).2]
    ring
theorem sum_powersetCard_prod_mul_sum_eq_pointed {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (p r : ι → ℝ) :
    (∑ S ∈ s.powersetCard (k + 1), (∏ j ∈ S, p j) * (∑ i ∈ S, r i)) =
      ∑ i ∈ s, (p i * r i) * coexposureEsymm (s.erase i) k p := by
  simp_rw [mul_sum]
  calc
    _ = ∑ i ∈ s, ∑ S ∈ (s.powersetCard (k + 1)).filter (fun S ↦ i ∈ S),
        (∏ j ∈ S, p j) * r i :=
      sum_comm' fun S i ↦
        ⟨fun h ↦ ⟨mem_filter.mpr h, (mem_powersetCard.mp h.1).1 h.2⟩,
          fun h ↦ mem_filter.mp h.1⟩
    _ = _ := by
      refine sum_congr rfl fun i hi ↦ ?_
      rw [sum_supports_containing_eq hi k p r, coexposureEsymm, mul_sum]
private theorem coexposureEsymm_erase_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i : ι) (k : ℕ) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) :
    coexposureEsymm (s.erase i) k p ≤ coexposureEsymm s k p :=
  sum_le_sum_of_subset_of_nonneg (powersetCard_mono (erase_subset _ _))
    (fun _ _ _ ↦ prod_nonneg fun i _ ↦ hp i)
private theorem factorial_mul_esymm_le_descFactorial {n : ℕ} (hn : 0 < n) (k : ℕ)
    {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    (k.factorial : ℝ) * coexposureEsymm univ k p ≤
      (n.descFactorial k : ℝ) / (n : ℝ) ^ k := by
  calc
    _ ≤ (k.factorial : ℝ) * ((n.choose k : ℝ) * (1 / (n : ℝ)) ^ k) :=
      mul_le_mul_of_nonneg_left (coexposureEsymm_le_uniform hn k hp hp1) (Nat.cast_nonneg _)
    _ = _ := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, one_div_pow, ← mul_assoc,
        mul_one_div]
theorem weightedSupportLengthSum_le {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (_hkn : k ≤ n)
    {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ((k - 1).factorial : ℝ) *
      (∑ S ∈ (univ : Finset (Fin n)).powersetCard k, (∏ i ∈ S, p i) * (τ + ∑ i ∈ S, p i)) ≤
      (τ / (k : ℝ)) * ((n.descFactorial k : ℝ) / (n : ℝ) ^ k) +
        (∑ i, p i ^ 2) * ((n.descFactorial (k - 1) : ℝ) / (n : ℝ) ^ (k - 1)) := by
  have hk0 : 0 < k := by omega
  have hkR : (k : ℝ) ≠ 0 := (Nat.cast_pos.mpr hk0).ne'
  have hkfac : (k : ℝ) * ((k - 1).factorial : ℝ) = (k.factorial : ℝ) := by
    exact_mod_cast Nat.mul_factorial_pred hk0.ne'
  have hpoint := sum_powersetCard_prod_mul_sum_eq_pointed univ (k - 1) p p
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hpoint
  simp_rw [← pow_two] at hpoint
  have hsplit :
      (∑ S ∈ (univ : Finset (Fin n)).powersetCard k, (∏ i ∈ S, p i) * (τ + ∑ i ∈ S, p i)) =
        τ * coexposureEsymm univ k p + ∑ i, p i ^ 2 * coexposureEsymm (univ.erase i) (k - 1) p := by
    simp_rw [mul_add]
    rw [sum_add_distrib, hpoint, coexposureEsymm, ← sum_mul, mul_comm _ τ]
  rw [hsplit, mul_add]
  refine add_le_add ?_ ?_
  · calc
      _ = (τ / (k : ℝ)) * ((k.factorial : ℝ) * coexposureEsymm univ k p) := by
        rw [← hkfac]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_mul_esymm_le_descFactorial hn k hp hp1)
        (div_nonneg hτ (Nat.cast_nonneg _))
  · calc
      _ ≤ ((k - 1).factorial : ℝ) *
          ∑ i, p i ^ 2 * coexposureEsymm univ (k - 1) p :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
            (coexposureEsymm_erase_le univ i (k - 1) hp) (sq_nonneg _)) (Nat.cast_nonneg _)
      _ = (∑ i, p i ^ 2) * (((k - 1).factorial : ℝ) * coexposureEsymm univ (k - 1) p) := by
        rw [← sum_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (factorial_mul_esymm_le_descFactorial hn (k - 1) hp hp1)
        (sum_nonneg fun i _ ↦ sq_nonneg _)
end StepA2
end

-- SingletonGaussianLength
section
open scoped BigOperators
open Finset
namespace StepA2
private theorem perturbedDescFactorial_le {n j k : ℕ} (hn : 0 < n) (hjn : j ≤ n)
    (hkj : k ≤ j + 1) (hkj₂ : k ≤ 2 * j) {η : ℝ}
    (hη₀ : 0 ≤ η) (hη : η ≤ 1 / Real.sqrt (n : ℝ)) :
    (1 + η) ^ k * ((n.descFactorial j : ℝ) / (n : ℝ) ^ j) ≤
      Real.exp 4 * Real.exp (-(k : ℝ) ^ 2 / (16 * (n : ℝ))) := by
  let r := Real.sqrt (n : ℝ)
  let t := (j : ℝ) / r
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr₂ : r ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hr₁ : 1 ≤ r := by
    change 1 ≤ Real.sqrt (n : ℝ)
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht₂ : (j : ℝ) ^ 2 / (n : ℝ) = t ^ 2 := by
    rw [show t ^ 2 = (j : ℝ) ^ 2 / r ^ 2 by simp [t, div_pow], hr₂]
  have ht₁ : (j : ℝ) / (n : ℝ) ≤ t := by
    rw [← hr₂, pow_two, ← div_div]
    exact div_le_self ht hr₁
  have hkη : (k : ℝ) * η ≤ t + 1 := calc
    _ ≤ (k : ℝ) * (1 / r) := mul_le_mul_of_nonneg_left hη (Nat.cast_nonneg k)
    _ ≤ ((j : ℝ) + 1) * (1 / r) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkj) (by positivity)
    _ = t + 1 / r := by dsimp [t]; ring
    _ ≤ t + 1 := add_le_add_right ((div_le_one hr).mpr hr₁) _
  have hk₂ : (k : ℝ) ^ 2 / (16 * (n : ℝ)) ≤ t ^ 2 / 4 := by
    have hk' : (k : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast hkj₂
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) k) hk' 2
    have hdiv := div_le_div_of_nonneg_right hpow
      (show 0 ≤ 16 * (n : ℝ) by positivity)
    rw [← ht₂]
    calc
      _ ≤ (2 * (j : ℝ)) ^ 2 / (16 * (n : ℝ)) := hdiv
      _ = (j : ℝ) ^ 2 / (n : ℝ) / 4 := by ring
  have hexp : (k : ℝ) * η - (j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ)) ≤
      4 - (k : ℝ) ^ 2 / (16 * (n : ℝ)) := calc
    _ = (k : ℝ) * η - ((j : ℝ) ^ 2 / (n : ℝ) - (j : ℝ) / (n : ℝ)) / 2 := by
      ring
    _ ≤ 1 + 3 * t / 2 - t ^ 2 / 2 := by rw [ht₂]; linarith only [hkη, ht₁]
    _ ≤ 4 - t ^ 2 / 4 := by nlinarith only [sq_nonneg (t - 3)]
    _ ≤ 4 - (k : ℝ) ^ 2 / (16 * (n : ℝ)) := by linarith only [hk₂]
  calc
    _ ≤ (Real.exp η) ^ k *
        Real.exp (-((j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ)))) :=
      mul_le_mul
        (pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp η) _)
        (descFactorial_div_pow_le_exp hn hjn) (by positivity) (by positivity)
    _ = Real.exp ((k : ℝ) * η - (j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      convert hexp using 1
      ring
theorem perturbedCycleLength_bound {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (hkn : k ≤ n)
    {η τ s : ℝ} (hη₀ : 0 ≤ η) (hη : η ≤ 1 / Real.sqrt (n : ℝ))
    (hτ : 0 ≤ τ) (hs : 0 ≤ s) :
    (1 + η) ^ k * (τ / (k : ℝ) * ((n.descFactorial k : ℝ) / (n : ℝ) ^ k) +
      s * ((n.descFactorial (k - 1) : ℝ) / (n : ℝ) ^ (k - 1))) ≤
      Real.exp 4 * Real.exp (-(k : ℝ) ^ 2 / (16 * (n : ℝ))) * (τ / (k : ℝ) + s) := by
  have hmain := perturbedDescFactorial_le hn hkn (show k ≤ k + 1 by omega)
    (show k ≤ 2 * k by omega) hη₀ hη
  have hpoint := perturbedDescFactorial_le hn (show k - 1 ≤ n by omega)
    (show k ≤ (k - 1) + 1 by omega) (show k ≤ 2 * (k - 1) by omega) hη₀ hη
  rw [mul_add, mul_add]
  apply add_le_add
  · convert mul_le_mul_of_nonneg_right hmain (div_nonneg hτ (Nat.cast_nonneg k)) using 1
    ring
  · convert mul_le_mul_of_nonneg_right hpoint hs using 1
    ring
private noncomputable def singletonLengthGaussian (n k : ℕ) : ℝ :=
  Real.exp (-(k : ℝ) ^ 2 / (16 * (n : ℝ)))
end StepA2
end

-- PivotSingletonLength
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
private def HasSoleForwardExposedLength {n : ℕ} (p : Profile n) (μ : Matching n) (k : ℕ) : Prop :=
  ∃ σ : Matching n, IsSoleForwardExposedRotation p μ σ ∧ σ.support.card = k
open scoped Classical in
theorem measureReal_soleForwardExposedLength_le_sum {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : Ω → Profile n) (μ : Matching n) (k : ℕ) :
    ν.real {x | HasSoleForwardExposedLength (P x) μ k} ≤
      ∑ σ ∈ Finset.univ.filter (fun σ : Matching n ↦ σ.IsCycle ∧ σ.support.card = k),
        ν.real {x | IsSoleForwardExposedRotation (P x) μ σ} := by
  let S := Finset.univ.filter (fun σ : Matching n ↦ σ.IsCycle ∧ σ.support.card = k)
  have heq : {x | HasSoleForwardExposedLength (P x) μ k} =
      ⋃ σ ∈ S, {x | IsSoleForwardExposedRotation (P x) μ σ} := by
    ext x
    simp only [mem_ofPred_eq, HasSoleForwardExposedLength, mem_iUnion,
      S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨σ, hσ, hk⟩ ↦ ⟨σ, ⟨(IsExposedRotation.isCycle hσ.1), hk⟩, hσ⟩,
      fun ⟨σ, hk, hσ⟩ ↦ ⟨σ, hσ, hk.2⟩⟩
  rw [heq]
  exact measureReal_biUnion_finset_le _ _
theorem measure_scoreStable_diagonal_rankEvent_le {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C)
    (hvalid : ∀ d ∈ C, (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) ∧
      ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1)
    (B : Set (Profile n)) {a : ℝ}
    (hrow : ∀ᵐ d ∂diagonalScoreLaw n, d ∈ C →
      (Measure.pi (normalizedStableScoreRowLaw d)).real
        {r | profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) ∈ B}
        ≤ a) :
    continuousScoreLaw n
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ profileOfScores x ∈ B} ≤
      continuousScoreLaw n {x | IsScoreStable x μ} * ENNReal.ofReal a := by
  let G : Set (ScoreProfile n) := profileOfScores ⁻¹' B
  let D : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}
  let f : ScoreProfile n → ℝ≥0∞ := G.indicator fun _ ↦ 1
  have hG : MeasurableSet G := measurable_profileOfScores n MeasurableSet.of_discrete
  have hf : Measurable f := measurable_const.indicator hG
  have hleft : continuousScoreLaw n
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ profileOfScores x ∈ B} =
      ∫⁻ x in D, f x ∂continuousScoreLaw n := by
    rw [show f = G.indicator (fun _ ↦ (1 : ℝ≥0∞)) from rfl, lintegral_indicator hG,
      lintegral_one, Measure.restrict_apply_univ, Measure.restrict_apply hG]
    congr 1
    ext x
    change (IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ profileOfScores x ∈ B) ↔
      (profileOfScores x ∈ B ∧ IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C)
    tauto
  rw [hleft, continuousScoreLaw_lintegral_stable_and_diagonal_rows μ hC hf]
  let m (d : DiagonalScorePairs n) := offDiagonalScoreLaw n (offDiagonalNonblocking d)
  have hM : (∫⁻ d, m d ∂diagonalScoreLaw n) = continuousScoreLaw n {x | IsScoreStable x μ} := by
    simpa only [mem_univ, and_true, indicator_univ, m] using
      (continuousScoreLaw_stable_and_diagonal μ (C := univ) MeasurableSet.univ).symm
  calc
    _ ≤ ∫⁻ d in C, m d * ENNReal.ofReal a ∂diagonalScoreLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hC, ae_restrict_of_ae hrow] with d hd hr
      obtain ⟨hx, hy⟩ := hvalid d hd
      let ν := Measure.pi (normalizedStableScoreRowLaw d)
      let : ∀ i : Fin n, IsProbabilityMeasure (normalizedStableScoreRowLaw d i) :=
        fun i ↦ normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
      let R := (splitScorePairs μ).symm ∘ fun r : OffDiagonalScoreRows n ↦
        (d, (offDiagonalRowsEquiv n).symm r)
      let E := R ⁻¹' G
      have hE : MeasurableSet E := hG.preimage
        ((splitScorePairs μ).symm.measurable.comp
          (measurable_const.prodMk (offDiagonalRowsEquiv n).symm.measurable))
      have hb : ν E ≤ ENNReal.ofReal a := by
        have h := ENNReal.ofReal_le_ofReal (hr hd)
        change ENNReal.ofReal ((ν E).toReal) ≤ _ at h
        rwa [ENNReal.ofReal_toReal (measure_ne_top ν E)] at h
      have hfun : (fun r ↦ f ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))) =
          E.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
        funext r
        change G.indicator (fun _ ↦ (1 : ℝ≥0∞)) (R r) = _
        by_cases he : r ∈ E
        · rw [indicator_of_mem (show R r ∈ G from he), indicator_of_mem he]
        · rw [indicator_of_notMem (show R r ∉ G from he), indicator_of_notMem he]
      rw [pi_stableScoreRowLaw_eq_smul_normalized d hx hy, hfun, lintegral_smul_measure,
        lintegral_indicator hE, lintegral_one, Measure.restrict_apply_univ, smul_eq_mul]
      exact mul_le_mul_right hb _
    _ ≤ ∫⁻ d, m d * ENNReal.ofReal a ∂diagonalScoreLaw n := lintegral_mono' Measure.restrict_le_self
      le_rfl
    _ = _ := by rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hM]
open scoped Classical in
theorem measureReal_soleForwardExposedLength_le_fallingFactorials {n k : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (P : Ω → Profile n) (μ : Matching n)
    (hn : 0 < n) (hk : 2 ≤ k) (hkn : k ≤ n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1) {τ η : ℝ}
    (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (hcycle : ∀ σ : Matching n, ν.real {x | IsSoleForwardExposedRotation (P x) μ σ} ≤
      ((1 + η) ^ σ.support.card * ∏ i ∈ σ.support, p i) *
        (Real.exp 1 * (τ + ∑ i ∈ σ.support, p i))) :
    ν.real {x | HasSoleForwardExposedLength (P x) μ k} ≤
      Real.exp 1 * ((1 + η) ^ k *
        ((τ / (k : ℝ)) * ((n.descFactorial k : ℝ) / (n : ℝ) ^ k) +
          (∑ i, p i ^ 2) * ((n.descFactorial (k - 1) : ℝ) / (n : ℝ) ^ (k - 1)))) := by
  let S := Finset.univ.filter (fun σ : Matching n ↦ σ.IsCycle ∧ σ.support.card = k)
  let F (A : Finset (Fin n)) := (∏ i ∈ A, p i) * (τ + ∑ i ∈ A, p i)
  have hc : 0 ≤ (1 + η) ^ k := pow_nonneg (by linarith only [hη]) _
  calc
    _ ≤ ∑ σ ∈ S, ν.real {x | IsSoleForwardExposedRotation (P x) μ σ} :=
      measureReal_soleForwardExposedLength_le_sum ν P μ k
    _ ≤ ∑ σ ∈ S, (((1 + η) ^ σ.support.card * ∏ i ∈ σ.support, p i) *
        (Real.exp 1 * (τ + ∑ i ∈ σ.support, p i))) :=
      Finset.sum_le_sum fun σ _ ↦ hcycle σ
    _ = Real.exp 1 * ((1 + η) ^ k * ∑ σ ∈ S, F σ.support) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      have hkσ : σ.support.card = k := (Finset.mem_filter.mp hσ).2.2
      rw [hkσ]
      unfold F
      ring
    _ = Real.exp 1 * ((1 + η) ^ k * (((k - 1).factorial : ℝ) *
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, F A)) := by
      rw [show (∑ σ ∈ S, F σ.support) = _ from sum_cyclesWithLength_by_support k hk F]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (weightedSupportLengthSum_le hn hk hkn hp hp₁ hτ) hc)
      (Real.exp_pos _).le
theorem ae_diagonal_measureReal_soleForwardExposedLength_le {n : ℕ}
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    (hn : 0 < n) (μ : Matching n)
    (hη₀ : 0 ≤ coexposureSuccessorPerturbation n)
    (hη : coexposureSuccessorPerturbation n ≤ 1 / Real.sqrt (n : ℝ))
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) :
    ∀ᵐ d ∂diagonalScoreLaw n,
      d ∈ goodDiagonalScores n →
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      ∀ (b : ℝ), HasForwardReferenceDeficit d b →
      ∀ k : ℕ, 2 ≤ k → k ≤ n →
        (Measure.pi (normalizedStableScoreRowLaw d)).real
          {r | HasSoleForwardExposedLength
            (profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))) μ k}
          ≤ Real.exp 5 * Real.exp (-(k : ℝ)^2 / (16 * (n : ℝ))) *
            ((b + ∑ i, (forwardSpouseWeight d i) ^ 2) / (k : ℝ) +
              ∑ i, (forwardSpouseWeight d i) ^ 2) := by
  filter_upwards [ae_diagonal_measureReal_soleForwardExposed_le_of_goodDiagonalScores μ hA hB hδ]
    with d hd
  intro hg hx hy b hb k hk hkn
  let p := forwardSpouseWeight d
  let s := ∑ i, p i ^ 2
  let τ := b + s
  let ν := Measure.pi (normalizedStableScoreRowLaw d)
  let P := fun r : OffDiagonalScoreRows n ↦
    profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))
  have hY : 0 < ∑ i, (diagonalPairAt d i).2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hg.1
  have hp (i : Fin n) : 0 ≤ p i := div_nonneg (hy i).1 hY.le
  have hp₁ : ∑ i, p i = 1 := by unfold p forwardSpouseWeight; rw [← Finset.sum_div, div_self hY.ne']
  have hs : 0 ≤ s := Finset.sum_nonneg fun i _ ↦ sq_nonneg (p i)
  have hb₀ : 0 ≤ b := by
    obtain ⟨δ, hδ, hd, _⟩ := hb
    exact (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (hδ i).1).trans hd
  have hτ : 0 ≤ τ := add_nonneg hb₀ hs
  have hcycle (σ : Matching n) :=
    hd hg hx hy b hb σ
  have hfinite := measureReal_soleForwardExposedLength_le_fallingFactorials
    ν P μ hn hk hkn hp hp₁ hτ hη₀ hcycle
  have hexp := mul_le_mul_of_nonneg_left
    (perturbedCycleLength_bound hn hk hkn hη₀ hη hτ hs) (Real.exp_pos 1).le
  refine hfinite.trans (hexp.trans_eq ?_)
  have h14 : Real.exp 1 * Real.exp 4 = Real.exp 5 := by rw [← Real.exp_add]; norm_num
  rw [← mul_assoc, ← mul_assoc, h14]
end StepA2
end

-- SingletonAnchorCounting
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal StepA2
namespace StepA2
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
open scoped Classical in
private noncomputable def singletonAnchorLengthWeight {W : Type*} [AddCommMonoid W]
    (p : Profile n) (μ : Matching n) (g : ℕ → W) : W :=
  ∑ σ : Matching n, if IsSoleForwardExposedRotation p μ σ then g σ.support.card else 0
open scoped Classical in
private noncomputable def profileSingletonAnchorLengthWeight {W : Type*} [AddCommMonoid W]
    (p : Profile n) (g : ℕ → W) : W :=
  ∑ μ : Matching n, if IsStable p μ then singletonAnchorLengthWeight p μ g else 0
private def scoreStableSingletonAnchorEvent (μ σ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ IsSoleForwardExposedRotation (profileOfScores x) μ σ}
theorem measurableSet_scoreStableSingletonAnchorEvent (μ σ : Matching n) :
    MeasurableSet (scoreStableSingletonAnchorEvent μ σ) :=
  (measurableSet_isScoreStable μ).inter
    ((measurable_profileOfScores n) (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | IsSoleForwardExposedRotation p μ σ}))
theorem lintegral_profileSingletonAnchorLengthWeight_eq_sum_scoreStableSingletonAnchorEvent
    (n : ℕ) (g : ℕ → ℝ≥0∞) :
    (∫⁻ p, profileSingletonAnchorLengthWeight p g ∂(uniformProfile n).toMeasure) =
      ∑ μ : Matching n, ∑ σ : Matching n,
        g σ.support.card * continuousScoreLaw n (scoreStableSingletonAnchorEvent μ σ) := by
  classical
  let f (μ σ : Matching n) := (scoreStableSingletonAnchorEvent μ σ).indicator
    (fun _ ↦ g σ.support.card)
  have hf (μ σ : Matching n) : Measurable (f μ σ) :=
    measurable_const.indicator (measurableSet_scoreStableSingletonAnchorEvent μ σ)
  have he : (fun x ↦ profileSingletonAnchorLengthWeight (profileOfScores x) g) =ᵐ[
      continuousScoreLaw n] fun x ↦ ∑ μ : Matching n, ∑ σ : Matching n, f μ σ x := by
    filter_upwards [ae_injective_rows n] with x hx
    unfold profileSingletonAnchorLengthWeight singletonAnchorLengthWeight
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    by_cases hμ : IsScoreStable x μ <;>
      simp [f, scoreStableSingletonAnchorEvent, Set.indicator,
        isStable_profileOfScores_iff hx μ, hμ]
  rw [← (measurePreserving_profileOfScores n).lintegral_comp Measurable.of_discrete,
    lintegral_congr_ae he, lintegral_finsetSum _ (fun μ _ ↦
      Finset.measurable_sum _ fun σ _ ↦ hf μ σ)]
  exact Finset.sum_congr rfl fun μ _ ↦ by
    rw [lintegral_finsetSum _ (fun σ _ ↦ hf μ σ)]
    exact Finset.sum_congr rfl fun σ _ ↦
      lintegral_indicator_const (measurableSet_scoreStableSingletonAnchorEvent μ σ) _
end StepA2
end

-- ForwardRowDeficitConcentration
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA2
private noncomputable def forwardWeightedEndpointError {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, (y i / spouseVectorTotal y) * Real.exp (-(1 - x i) * spouseVectorTotal y)
theorem measurable_forwardWeightedEndpointError (n : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ forwardWeightedEndpointError z.1 z.2) := by
  unfold forwardWeightedEndpointError spouseVectorTotal
  fun_prop
private theorem lintegral_stableMaleSpouseRowLaw_endpointError_le {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (-(1 - z) * spouseVectorTotal y))
      ∂stableMaleSpouseRowLaw y i) ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-spouseVectorTotal y)) := by
  let Y := spouseVectorTotal y
  let K := scoreRowKernel (Finset.univ.erase i) y
  have hK : Measurable (fun z ↦ ENNReal.ofReal (K z)) :=
    (continuous_scoreRowKernel _ _).measurable.ennreal_ofReal
  have hg : Measurable (fun z : ℝ ↦ ENNReal.ofReal (Real.exp (-(1 - z) * Y))) := by
    fun_prop
  have herase : (∑ j ∈ Finset.univ.erase i, y j) = Y - y i :=
    eq_sub_of_add_eq (Finset.sum_erase_add _ y (Finset.mem_univ i))
  unfold stableMaleSpouseRowLaw
  rw [lintegral_withDensity_eq_lintegral_mul _ hK hg]
  calc
    _ ≤ ∫⁻ _z, ENNReal.ofReal (Real.exp 1 * Real.exp (-Y)) ∂unitScoreLaw := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc :
        MeasurableSet (Icc (0 : ℝ) 1))] with z hz
      change ENNReal.ofReal (K z) * ENNReal.ofReal (Real.exp (-(1 - z) * Y)) ≤ _
      rw [mul_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have hkernel := scoreRowKernel_le_exp (J := Finset.univ.erase i)
        (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hz
      rw [herase] at hkernel
      calc
        _ ≤ Real.exp (-(1 - z) * Y) * Real.exp (-(Y - y i) * z) :=
          mul_le_mul_of_nonneg_left hkernel (Real.exp_pos _).le
        _ = Real.exp (y i * z) * Real.exp (-Y) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          ((mul_le_mul_of_nonneg_right (hy i).2 hz.1).trans (by simpa using hz.2)))
          (Real.exp_pos _).le
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]
theorem lintegral_normalizedStableMaleSpouseRowLaw_endpointError_le {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ spouseVectorTotal y) (i : Fin n) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (-(1 - z) * spouseVectorTotal y))
      ∂normalizedStableMaleSpouseRowLaw y i) ≤
      ENNReal.ofReal (4 * Real.exp 1 * spouseVectorTotal y *
        Real.exp (-spouseVectorTotal y)) := by
  let Y := spouseVectorTotal y
  have hY : 0 < Y := by linarith
  have hsum : ∑ j ∈ Finset.univ.erase i, y j ≤ Y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ ↦ (hy j).1
  have hmass : ENNReal.ofReal (1 / (4 * Y)) ≤ stableMaleSpouseRowLaw y i univ := by
    rw [stableMaleSpouseRowLaw_univ y hy i]
    exact ENNReal.ofReal_le_ofReal
      (scoreRowMass_lower (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) (by linarith) hsum)
  have hinv : (stableMaleSpouseRowLaw y i univ)⁻¹ ≤ ENNReal.ofReal (4 * Y) := by
    calc
      _ ≤ (ENNReal.ofReal (1 / (4 * Y)))⁻¹ := ENNReal.inv_le_inv.mpr hmass
      _ = _ := by
        rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
  rw [normalizedStableMaleSpouseRowLaw, lintegral_smul_measure, smul_eq_mul]
  calc
    _ ≤ ENNReal.ofReal (4 * Y) * ENNReal.ofReal (Real.exp 1 * Real.exp (-Y)) :=
      mul_le_mul' hinv (lintegral_stableMaleSpouseRowLaw_endpointError_le y hy i)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
theorem measure_pi_forwardWeightedEndpointError_gt_le {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ spouseVectorTotal y)
    {B : ℝ} (hB : 0 < B) (hp : ∀ i, y i / spouseVectorTotal y ≤ B) (t : ℝ) :
    (Measure.pi (normalizedStableMaleSpouseRowLaw y)) {x | t < forwardWeightedEndpointError x y} ≤
      ENNReal.ofReal (Real.exp ((-t + (Real.exp 1 - 1) *
        (4 * Real.exp 1 * spouseVectorTotal y * Real.exp (-spouseVectorTotal y))) / B)) := by
  let Y := spouseVectorTotal y
  let ν := normalizedStableMaleSpouseRowLaw y
  let p (i : Fin n) := y i / Y
  let g (i : Fin n) (z : ℝ) := p i * min (Real.exp (-(1 - z) * Y)) 1
  let C := 4 * Real.exp 1 * Y * Real.exp (-Y)
  have hY : 0 < Y := by linarith
  have (i : Fin n) : IsProbabilityMeasure (ν i) :=
    normalizedStableMaleSpouseRowLaw_isProbabilityMeasure y hy hs i
  have hp0 (i : Fin n) : 0 ≤ p i := div_nonneg (hy i).1 hY.le
  have hC : 0 ≤ C := by unfold C; positivity
  have hg (i : Fin n) : Measurable (g i) := by unfold g; fun_prop
  have hb (i : Fin n) (z : ℝ) : g i z ∈ Icc 0 B := by
    refine ⟨mul_nonneg (hp0 i) (le_min (Real.exp_pos _).le zero_le_one), ?_⟩
    exact (mul_le_of_le_one_right (hp0 i) (min_le_right _ _)).trans (hp i)
  have hmean (i : Fin n) : (∫⁻ z, ENNReal.ofReal (g i z) ∂ν i) ≤ ENNReal.ofReal (p i * C) := by
    have hExp : Measurable (fun z : ℝ ↦ ENNReal.ofReal (Real.exp (-(1 - z) * Y))) := by
      fun_prop
    calc
      _ ≤ ∫⁻ z, ENNReal.ofReal (p i) * ENNReal.ofReal (Real.exp (-(1 - z) * Y)) ∂ν i := by
        apply lintegral_mono
        intro z
        change ENNReal.ofReal (g i z) ≤
          ENNReal.ofReal (p i) * ENNReal.ofReal (Real.exp (-(1 - z) * Y))
        rw [← ENNReal.ofReal_mul (hp0 i)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_left _ _) (hp0 i))
      _ = ENNReal.ofReal (p i) * ∫⁻ z, ENNReal.ofReal (Real.exp (-(1 - z) * Y)) ∂ν i :=
        lintegral_const_mul _ hExp
      _ ≤ _ := by
        rw [ENNReal.ofReal_mul (hp0 i)]
        exact mul_le_mul_right
          (lintegral_normalizedStableMaleSpouseRowLaw_endpointError_le y hy hs i) _
  have hpSum : ∑ i, p i = 1 := by
    simp only [p, ← Finset.sum_div]
    exact div_self hY.ne'
  have hsum : (∑ i, p i * C) = C := by rw [← Finset.sum_mul, hpSum, one_mul]
  have hsupp : ∀ᵐ x ∂Measure.pi ν, ∀ i, x i ∈ Icc (0 : ℝ) 1 :=
    ae_all_iff.2 fun i ↦ (measurePreserving_eval ν i).quasiMeasurePreserving.ae
      (ae_normalizedStableMaleSpouseRowLaw_mem_Icc y i)
  have hsub : {x | t < forwardWeightedEndpointError x y} ≤ᵐ[Measure.pi ν]
      {x | t < ∑ i, g i (x i)} := by
    filter_upwards [hsupp] with x hx hxt
    have he (i : Fin n) : min (Real.exp (-(1 - x i) * Y)) 1 =
        Real.exp (-(1 - x i) * Y) :=
      min_eq_left (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr (hx i).2)) hY.le))
    change t < ∑ i, g i (x i)
    change t < ∑ i, p i * Real.exp (-(1 - x i) * Y) at hxt
    simpa only [g, he] using hxt
  refine (measure_mono_ae hsub).trans ?_
  simpa only [hsum] using measure_pi_boundedSum_gt_le ν g hg hB hb (fun i ↦ p i * C)
    (fun i ↦ mul_nonneg (hp0 i) hC) hmean t
end StepA2
end

-- MarkedForwardRowDeficit
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
private theorem eventually_forwardEndpointMean_le :
    ∀ᶠ n : ℕ in atTop, ∀ Y : ℝ, (9 / 10 : ℝ) * Real.log n ≤ Y →
      (Real.exp 1 - 1) * (4 * Real.exp 1 * Y * Real.exp (-Y)) ≤
        (n : ℝ) ^ (-3 / 4 : ℝ) / 2 := by
  let C := 40 * Real.exp 1 * (Real.exp 1 - 1)
  have he₁ : 0 ≤ Real.exp 1 - 1 := by linarith only [Real.exp_one_gt_two]
  have hC : 0 ≤ C := by
    unfold C
    positivity
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (3 / 50 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_gt_atTop (0 : ℕ), hpow.eventually_ge_atTop (2 * C)] with n hn hc
  intro Y hY
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsmall : Y ≤ 10 * Real.exp (Y / 10) := by
    linarith only [Real.add_one_le_exp (Y / 10)]
  have hfactor : 0 ≤ 4 * Real.exp 1 * (Real.exp 1 - 1) * Real.exp (-Y) := by
    positivity
  have he : Real.exp (-(9 / 10 : ℝ) * Y) ≤ (n : ℝ) ^ (-81 / 100 : ℝ) := by
    rw [Real.rpow_def_of_pos hn₀]
    apply Real.exp_le_exp.mpr
    linarith only [hY]
  have hd : C ≤ (n : ℝ) ^ (3 / 50 : ℝ) / 2 := by linarith only [hc]
  calc
    _ = Y * (4 * Real.exp 1 * (Real.exp 1 - 1) * Real.exp (-Y)) := by ring
    _ ≤ (10 * Real.exp (Y / 10)) *
        (4 * Real.exp 1 * (Real.exp 1 - 1) * Real.exp (-Y)) :=
      mul_le_mul_of_nonneg_right hsmall hfactor
    _ = C * Real.exp (-(9 / 10 : ℝ) * Y) := by
      rw [show -(9 / 10 : ℝ) * Y = Y / 10 + -Y by ring, Real.exp_add]
      unfold C
      ring
    _ ≤ C * (n : ℝ) ^ (-81 / 100 : ℝ) := mul_le_mul_of_nonneg_left he hC
    _ ≤ ((n : ℝ) ^ (3 / 50 : ℝ) / 2) * (n : ℝ) ^ (-81 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hn₀.le _)
    _ = _ := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hn₀]
      congr 2
      norm_num
private theorem eventually_forwardEndpointRate_le (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-((n : ℝ) ^ (-3 / 4 : ℝ) / 2) /
      (12 * Real.log n / n)) ≤ (n : ℝ) ^ (-q) := by
  have h := (((isLittleO_log_rpow_rpow_atTop (s := (1 / 4 : ℝ)) 2 (by norm_num)).const_mul_left
    (24 * q)).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (1 : ℕ), h] with n hn hh
  have hn₁ : 1 < (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith only [hn₁]
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn₁
  have habs : |(24 * q) * Real.log (n : ℝ) ^ (2 : ℝ)| ≤ |(n : ℝ) ^ (1 / 4 : ℝ)| := hh
  rw [abs_of_nonneg (Real.rpow_nonneg hn₀.le _), Real.rpow_two] at habs
  have hle := (le_abs_self _).trans habs
  have hB : 0 < 12 * Real.log (n : ℝ) / n := by positivity
  have hp : (n : ℝ) ^ (-3 / 4 : ℝ) * n = (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ = (n : ℝ) ^ (-3 / 4 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn₀]; norm_num
  have haux : q * Real.log (n : ℝ) ≤
      ((n : ℝ) ^ (-3 / 4 : ℝ) / 2) / (12 * Real.log n / n) := by
    apply (le_div_iff₀ hB).mpr
    rw [← mul_div_assoc, div_le_iff₀ hn₀, div_mul_eq_mul_div, hp, le_div_iff₀ (by norm_num)]
    linarith only [hle]
  rw [show (n : ℝ) ^ (-q) = Real.exp (Real.log n * -q) from Real.rpow_def_of_pos hn₀ _]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  linarith only [haux]
private def badForwardEndpointVectors (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | (2 ≤ spouseVectorTotal z.2 ∧ (9 / 10 : ℝ) * Real.log n ≤ spouseVectorTotal z.2 ∧
      ∀ i, z.2 i / spouseVectorTotal z.2 ≤ 12 * Real.log n / n) ∧
    (n : ℝ) ^ (-3 / 4 : ℝ) < forwardWeightedEndpointError z.1 z.2}
theorem measurableSet_badForwardEndpointVectors (n : ℕ) :
    MeasurableSet (badForwardEndpointVectors n) := by
  have hY : Measurable fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ spouseVectorTotal z.2 :=
    (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i).comp measurable_snd
  unfold badForwardEndpointVectors
  simp only [ofPred_and, ofPred_forall]
  exact ((measurableSet_le measurable_const hY).inter
    ((measurableSet_le measurable_const hY).inter
      (MeasurableSet.iInter fun i ↦ measurableSet_le
        (((measurable_pi_apply i).comp measurable_snd).div hY) measurable_const))).inter
    (measurableSet_lt measurable_const (measurable_forwardWeightedEndpointError n))
private theorem eventually_forwardEndpointSection_le (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ y : Fin n → ℝ, (∀ j, y j ∈ Icc (0 : ℝ) 1) →
      (∫⁻ x, (badForwardEndpointVectors n).indicator
        (fun z ↦ spouseStabilityKernel z.1 z.2) (x, y) ∂spouseVectorLaw n) ≤
      femaleSpouseStabilityDensity y * ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  filter_upwards [eventually_forwardEndpointMean_le, eventually_forwardEndpointRate_le q,
    eventually_gt_atTop (1 : ℕ)] with n hmean hrate hn
  intro y hy
  let Y := spouseVectorTotal y
  let B := {x : Fin n → ℝ | (n : ℝ) ^ (-3 / 4 : ℝ) < forwardWeightedEndpointError x y}
  by_cases hg : 2 ≤ Y ∧ (9 / 10 : ℝ) * Real.log n ≤ Y ∧
      ∀ i, y i / Y ≤ 12 * Real.log n / n
  · have hB : MeasurableSet B := measurableSet_lt measurable_const
      ((measurable_forwardWeightedEndpointError n).comp (measurable_id.prodMk measurable_const))
    have hpoint (x : Fin n → ℝ) :
        (badForwardEndpointVectors n).indicator (fun z ↦ spouseStabilityKernel z.1 z.2)
          (x, y) = B.indicator (fun x ↦ spouseStabilityKernel x y) x := by
      have hmem : (x, y) ∈ badForwardEndpointVectors n ↔ x ∈ B := and_iff_right hg
      by_cases hx : x ∈ B
      · rw [indicator_of_mem (hmem.mpr hx), indicator_of_mem hx]
      · rw [indicator_of_notMem (hmem.not.mpr hx), indicator_of_notMem hx]
    have hn₁ : 1 < (n : ℝ) := by exact_mod_cast hn
    have hlog := Real.log_pos hn₁
    have hwidth : 0 < 12 * Real.log (n : ℝ) / n := by positivity
    simp_rw [hpoint]
    rw [lintegral_indicator hB, ← withDensity_apply _ hB,
      spouseStabilityKernel_withDensity_eq y hy hg.1, Measure.smul_apply, smul_eq_mul]
    apply mul_le_mul_right
    refine (measure_pi_forwardWeightedEndpointError_gt_le y hy hg.1 hwidth hg.2.2 _).trans ?_
    apply ENNReal.ofReal_le_ofReal
    refine (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hwidth).mpr ?_)).trans hrate
    linarith only [hmean Y hg.2.1]
  · have hz (x : Fin n → ℝ) :
        (badForwardEndpointVectors n).indicator (fun z ↦ spouseStabilityKernel z.1 z.2)
          (x, y) = 0 := indicator_of_notMem (fun h ↦ hg h.1) _
    simp_rw [hz, lintegral_zero]
    exact zero_le
private def badForwardEndpointMark {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧
    ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ badForwardEndpointVectors n}
theorem eventually_sum_measure_badForwardEndpointMark_le (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, (∑ μ : Matching n, continuousScoreLaw n (badForwardEndpointMark μ)) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  filter_upwards [eventually_forwardEndpointSection_le (q + 2),
    eventually_expectedNumStableMatchings_le_sizeSq, eventually_gt_atTop (0 : ℕ)]
    with n hsec hmean hn
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  calc
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ} *
        ENNReal.ofReal ((n : ℝ) ^ (-(q + 2))) := Finset.sum_le_sum fun μ _ ↦
      measure_stable_and_spouseVectors_le_of_section μ (measurableSet_badForwardEndpointVectors n)
        ENNReal.ofReal_ne_top hsec
    _ = ENNReal.ofReal (expectedNumStableMatchings n) *
        ENNReal.ofReal ((n : ℝ) ^ (-(q + 2))) := by
      rw [← Finset.sum_mul, sum_measure_scoreStable_eq_expected]
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (2 : ℕ)) * ENNReal.ofReal ((n : ℝ) ^ (-(q + 2))) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hmean) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_two, ← Real.rpow_add hn₀,
        show (2 : ℝ) + -(q + 2) = -q by ring]
end StepA2
end

-- SingletonDiagonalExceptions
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
private def singletonLengthGoodDiagonal (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | d ∈ goodDiagonalScores n ∧
    (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) ∧
    (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) ∧
    (9 / 10 : ℝ) * Real.log n ≤ pivotDiagonalFemaleTotal d ∧
    (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ) ∧
    (∑ i, forwardSpouseWeight d i *
      Real.exp (-((1 - (diagonalPairAt d i).1) * pivotDiagonalFemaleTotal d))) ≤
      (n : ℝ) ^ (-3 / 4 : ℝ)}
theorem measurableSet_singletonLengthGoodDiagonal (n : ℕ) :
    MeasurableSet (singletonLengthGoodDiagonal n) := by
  have hx (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).1) :=
    measurable_fst.comp (measurable_pi_apply _)
  have hy (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).2) :=
    measurable_snd.comp (measurable_pi_apply _)
  have hY : Measurable (@pivotDiagonalFemaleTotal n) :=
    Finset.measurable_sum _ fun i _ ↦ hy i
  have hw (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ forwardSpouseWeight d i) :=
    (hy i).div hY
  have hsq : Measurable (fun d : DiagonalScorePairs n ↦ ∑ i, (forwardSpouseWeight d i) ^ 2) :=
    Finset.measurable_sum _ fun i _ ↦ (hw i).pow_const _
  have hend : Measurable (fun d : DiagonalScorePairs n ↦ ∑ i, forwardSpouseWeight d i *
      Real.exp (-((1 - (diagonalPairAt d i).1) * pivotDiagonalFemaleTotal d))) :=
    Finset.measurable_sum _ fun i _ ↦ (hw i).mul
      (Real.measurable_exp.comp (((measurable_const.sub (hx i)).mul hY).neg))
  unfold singletonLengthGoodDiagonal
  simp only [ofPred_and, ofPred_forall]
  exact (measurableSet_goodDiagonalScores n).inter
    ((MeasurableSet.iInter fun i ↦ measurableSet_Ico.preimage (hx i)).inter
      ((MeasurableSet.iInter fun i ↦ measurableSet_Icc.preimage (hy i)).inter
        ((measurableSet_le measurable_const hY).inter
          ((measurableSet_le hsq measurable_const).inter
            (measurableSet_le hend measurable_const)))))
theorem eventually_hasForwardReferenceDeficit_of_singletonLengthGoodDiagonal :
    ∀ᶠ n : ℕ in atTop, ∀ d ∈ singletonLengthGoodDiagonal n,
      HasForwardReferenceDeficit d (3 * (n : ℝ) ^ (-3 / 4 : ℝ)) := by
  filter_upwards [eventually_hasForwardReferenceDeficit] with n h d hd
  exact h d hd.2.1 hd.2.2.1 hd.1.1 hd.1.2.1 hd.1.2.2 hd.2.2.2.2.2
private def badSingletonSmallTotal {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
private def badSingletonRelativeShare {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ largeRelativeSpouseScoreSet n}
private theorem measure_badSingletonLengthDiagonal_le {n : ℕ} (hn : 0 < n)
    (hlog : 2 ≤ (9 / 10 : ℝ) * Real.log n) (μ : Matching n) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧
        (splitScorePairs μ x).1 ∉ singletonLengthGoodDiagonal n} ≤
      continuousScoreLaw n (badSingletonSmallTotal μ) +
        continuousScoreLaw n (badSingletonRelativeShare μ) +
        continuousScoreLaw n (badMaleSpouseScores μ) +
        continuousScoreLaw n (badFemaleSpouseSquareMark μ) +
        continuousScoreLaw n (badForwardEndpointMark μ) := by
  let exceptions : Set (ScoreProfile n) :=
    (((badSingletonSmallTotal μ ∪ badSingletonRelativeShare μ) ∪ badMaleSpouseScores μ) ∪
      badFemaleSpouseSquareMark μ) ∪ badForwardEndpointMark μ
  have hsub : {x | IsScoreStable x μ ∧
        (splitScorePairs μ x).1 ∉ singletonLengthGoodDiagonal n} ≤ᵐ[continuousScoreLaw n]
      exceptions := by
    filter_upwards [ae_unitOpen_scores n] with x hx hbad
    let d := (splitScorePairs μ x).1
    let xm (i : Fin n) := maleSpouseScore x μ i
    let yf := femaleSpouseByHusband μ x
    have hm (i : Fin n) : (diagonalPairAt d i).1 = xm i :=
      congrArg Prod.fst (diagonalPairAt_splitScorePairs μ x i)
    have hf (i : Fin n) : (diagonalPairAt d i).2 = yf i := by
      simp only [d, diagonalPairAt_splitScorePairs, yf, femaleSpouseByHusband, femaleSpouseScore,
        Equiv.symm_apply_apply]
    have hY : pivotDiagonalFemaleTotal d = spouseVectorTotal yf :=
      Finset.sum_congr rfl fun i _ ↦ hf i
    have hY' : spouseVectorTotal yf = femaleSpouseTotal x μ :=
      (femaleSpouseTotal_eq_sum_byHusband μ x).symm
    have hw (i : Fin n) : forwardSpouseWeight d i = spouseAngle yf i := by
      change (diagonalPairAt d i).2 / pivotDiagonalFemaleTotal d = yf i / spouseVectorTotal yf
      rw [hf i, hY]
    have hy (i : Fin n) : yf i ∈ Ioo (0 : ℝ) 1 :=
      hx (.inr (μ i)) (μ.symm (μ i))
    by_cases hsmall : femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hbad.1, hsmall⟩)))
    have hlarge : 2 ≤ femaleSpouseTotal x μ := hlog.trans (le_of_not_gt hsmall)
    by_cases hshare : ∀ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤
        12 * Real.log n / n
    · by_cases hmale : ∀ i, maleSpouseScore x μ i ≤
          8 * Real.log n / (femaleSpouseTotal x μ - 1)
      · by_cases hsquare : (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ)
        · by_cases hend : forwardWeightedEndpointError xm yf ≤ (n : ℝ) ^ (-3 / 4 : ℝ)
          · exfalso
            apply hbad.2
            refine ⟨(mem_goodDiagonalScores_iff x μ).mpr ⟨hlarge, hshare, hmale⟩,
              ?_, ?_, ?_, hsquare, ?_⟩
            · intro i
              rw [hm i]
              exact ⟨(hx (.inl i) (μ i)).1.le, (hx (.inl i) (μ i)).2⟩
            · intro i
              rw [hf i]
              exact ⟨(hy i).1.le, (hy i).2.le⟩
            · rw [hY, hY']
              exact le_of_not_gt hsmall
            · change (∑ i, forwardSpouseWeight d i *
                  Real.exp (-((1 - (diagonalPairAt d i).1) * pivotDiagonalFemaleTotal d))) ≤ _
              simp_rw [hw, hm, hY]
              simpa only [forwardWeightedEndpointError, spouseAngle, spouseVectorTotal, neg_mul] using hend
          · exact Or.inr ⟨hbad.1, ⟨hY'.symm ▸ hlarge, hY'.symm ▸ le_of_not_gt hsmall,
              fun i ↦ by rw [hY']; exact hshare (μ i)⟩, lt_of_not_ge hend⟩
        · apply Or.inl
          apply Or.inr
          refine ⟨hbad.1, ?_⟩
          have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
          have h := (div_lt_iff₀ hn₀).mp (lt_of_not_ge hsquare)
          simpa only [largeSpouseAngularSquareSet, mem_ofPred_eq, pittelAngularSquareScore, hw,
            mul_comm] using h
      · obtain ⟨i, hi⟩ := not_forall.mp hmale
        exact Or.inl (Or.inl (Or.inr ⟨hbad.1, hlarge, i, lt_of_not_ge hi⟩))
    · obtain ⟨j, hj⟩ := not_forall.mp hshare
      have htotal : spouseVectorTotal yf ≤ (n : ℝ) := by
        calc
          _ ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ (hy i).2.le
          _ = _ := by simp
      refine Or.inl (Or.inl (Or.inl (Or.inr ⟨hbad.1, fun i ↦ (hy i).1.le, hY'.symm ▸ hlarge,
        htotal, μ.symm j, ?_⟩)))
      change 12 * Real.log n / n < yf (μ.symm j) / spouseVectorTotal yf
      rw [hY']
      simpa only [yf, femaleSpouseByHusband, Equiv.apply_symm_apply] using lt_of_not_ge hj
  calc
    _ ≤ continuousScoreLaw n exceptions := measure_mono_ae hsub
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)) le_rfl)
private theorem neg_four_rpow_eq_inv {z : ℝ} (hz : 0 ≤ z) :
    z ^ (-4 : ℝ) = (z ^ (4 : ℕ))⁻¹ := by
  rw [Real.rpow_neg hz, Real.rpow_ofNat]
private theorem eventually_sum_badSingletonRelativeShare_le :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n (badSingletonRelativeShare μ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-4 : ℝ)) := by
  have hexp : ∀ᶠ n : ℕ in atTop, Real.exp (5 / 2 : ℝ) ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  filter_upwards [eventually_coexposureSuccessorPerturbation_bounds, hexp,
    eventually_ge_atTop (2 : ℕ)] with n h he hn
  have hn₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr h.1
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith only [hn₂])
  have hcut : 12 * Real.log n / (n : ℝ) ≤ 1 := by
    linarith only [h.2.2.2.2.1, div_nonneg hnlog hn₀.le,
      show 24 * Real.log n / (n : ℝ) = 2 * (12 * Real.log n / (n : ℝ)) by ring]
  refine (sum_stable_largeRelativeSpouseScore_le h.1 hcut).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [neg_four_rpow_eq_inv hn₀.le]
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) ^ (12 : ℕ))).mpr
  have hcube : (n : ℝ) ^ 2 + 1 ≤ (n : ℝ) ^ 3 := by
    nlinarith only [hn₂, mul_nonneg (sub_nonneg.mpr hn₂) (sq_nonneg (n : ℝ))]
  calc
    _ ≤ ((n : ℝ) ^ 3 * n) * n := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hcube hn₀.le) he
        (Real.exp_nonneg _) (by positivity)
    _ = (n : ℝ) ^ 5 := by ring
    _ ≤ (n : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith only [hn₂]) (by norm_num)
    _ = _ := by field_simp
private theorem eventually_sum_badSingletonMaleScore_le :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n (badMaleSpouseScores μ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-4 : ℝ)) := by
  filter_upwards [eventually_expectedNumStableMatchings_le_sizeSq,
    eventually_ge_atTop (8 : ℕ)] with n hmean hn
  have hn₈ : 8 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith only [hn₈]
  calc
    _ ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 7) * ENNReal.ofReal (expectedNumStableMatchings n) :=
      sum_measure_badMaleSpouseScores_le (Nat.cast_pos.mp hn₀)
    _ ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 7) * ENNReal.ofReal ((n : ℝ) ^ 2) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hmean)
    _ = ENNReal.ofReal ((8 / (n : ℝ) ^ 7) * (n : ℝ) ^ 2) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      rw [neg_four_rpow_eq_inv hn₀.le, div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) ^ (7 : ℕ))).mpr
      calc
        _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hn₈ (sq_nonneg _)
        _ = _ := by field_simp)
theorem eventually_sum_measure_badSingletonLengthDiagonal_le :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ ∧
        (splitScorePairs μ x).1 ∉ singletonLengthGoodDiagonal n}) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ)) := by
  have hlog : ∀ᶠ n : ℕ in atTop, 2 ≤ (9 / 10 : ℝ) * Real.log n :=
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (20 / 9)).mono fun n h ↦ by
        change (20 / 9 : ℝ) ≤ Real.log (n : ℝ) at h
        linarith only [h]
  filter_upwards [eventually_sum_stable_smallSpouseTotalLog_le 4,
    eventually_sum_badSingletonRelativeShare_le, eventually_sum_badSingletonMaleScore_le,
    eventually_sum_measure_badFemaleSpouseSquareMark_le 4 (by norm_num),
    eventually_sum_measure_badForwardEndpointMark_le 4, hlog, eventually_ge_atTop (5 : ℕ)]
    with n hsmall hshare hmale hsq hend hlog hn
  have hn₅ : 5 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith only [hn₅]
  let a := (n : ℝ) ^ (-4 : ℝ)
  have ha : 0 ≤ a := Real.rpow_nonneg hn₀.le _
  calc
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n (badSingletonSmallTotal μ) +
          continuousScoreLaw n (badSingletonRelativeShare μ) +
          continuousScoreLaw n (badMaleSpouseScores μ) +
          continuousScoreLaw n (badFemaleSpouseSquareMark μ) +
          continuousScoreLaw n (badForwardEndpointMark μ)) :=
      Finset.sum_le_sum fun μ _ ↦ measure_badSingletonLengthDiagonal_le
        (Nat.cast_pos.mp hn₀) hlog μ
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal a + ENNReal.ofReal a +
        ENNReal.ofReal a + ENNReal.ofReal a := by
      simp only [Finset.sum_add_distrib]
      exact add_le_add (add_le_add (add_le_add (add_le_add hsmall hshare) hmale) hsq) hend
    _ = ENNReal.ofReal (5 * a) := by
      repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (calc
      5 * a ≤ (n : ℝ) * a := mul_le_mul_of_nonneg_right hn₅ ha
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-4 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn₀, show (1 : ℝ) + -4 = -3 by norm_num])
end StepA2
end

-- PivotSingletonMarkedLength
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
private def scoreStableSingletonLengthEvent {n : ℕ} (μ : Matching n)
    (C : Set (DiagonalScorePairs n)) (k : ℕ) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧
    HasSoleForwardExposedLength (profileOfScores x) μ k}
theorem measurableSet_scoreStableSingletonLengthEvent {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) (k : ℕ) :
    MeasurableSet (scoreStableSingletonLengthEvent μ C k) :=
  (measurableSet_isScoreStable μ).inter
    (((measurable_fst.comp (splitScorePairs μ).measurable) hC).inter
      (measurable_profileOfScores n (MeasurableSet.of_discrete :
        MeasurableSet {p : Profile n | HasSoleForwardExposedLength p μ k})))
private def badSingletonLengthDiagonalEvent {n : ℕ} (μ : Matching n)
    (C : Set (DiagonalScorePairs n)) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∉ C}
theorem measurableSet_badSingletonLengthDiagonalEvent {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) :
    MeasurableSet (badSingletonLengthDiagonalEvent μ C) :=
  (measurableSet_isScoreStable μ).inter
    ((measurable_fst.comp (splitScorePairs μ).measurable) hC.compl)
open scoped Classical in
private theorem sum_singletonAnchor_indicators_le {n : ℕ} (μ : Matching n)
    (C : Set (DiagonalScorePairs n)) (g : ℕ → ℝ≥0∞) {B : ℝ≥0∞}
    (hB : ∀ k ∈ Finset.Icc 2 n, g k ≤ B) (x : ScoreProfile n) :
    (∑ σ : Matching n, (scoreStableSingletonAnchorEvent μ σ).indicator
      (fun _ ↦ g σ.support.card) x) ≤
      (∑ k ∈ Finset.Icc 2 n, (scoreStableSingletonLengthEvent μ C k).indicator
        (fun _ ↦ g k) x) + (badSingletonLengthDiagonalEvent μ C).indicator (fun _ ↦ B) x := by
  by_cases he : ∃ σ : Matching n, x ∈ scoreStableSingletonAnchorEvent μ σ
  · obtain ⟨σ, hx⟩ := he
    have hsum : (∑ ρ : Matching n, (scoreStableSingletonAnchorEvent μ ρ).indicator
        (fun _ ↦ g ρ.support.card) x) = g σ.support.card := by
      rw [Finset.sum_eq_single σ]
      · exact indicator_of_mem hx _
      · intro ρ _ hne
        exact indicator_of_notMem (fun h ↦ hne (hx.2.2 ρ h.2.1)) _
      · simp
    rw [hsum]
    have hk : σ.support.card ∈ Finset.Icc 2 n := Finset.mem_Icc.mpr
      ⟨(IsExposedRotation.isCycle hx.2.1).two_le_card_support, (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)⟩
    by_cases hd : (splitScorePairs μ x).1 ∈ C
    · have hmem : x ∈ scoreStableSingletonLengthEvent μ C σ.support.card :=
        ⟨hx.1, hd, σ, hx.2, rfl⟩
      have hle : g σ.support.card ≤
          ∑ k ∈ Finset.Icc 2 n, (scoreStableSingletonLengthEvent μ C k).indicator
            (fun _ ↦ g k) x := by
        calc
          _ = (scoreStableSingletonLengthEvent μ C σ.support.card).indicator
              (fun _ ↦ g σ.support.card) x := (indicator_of_mem hmem _).symm
          _ ≤ _ := Finset.single_le_sum
            (f := fun k ↦ (scoreStableSingletonLengthEvent μ C k).indicator (fun _ ↦ g k) x)
            (fun _ _ ↦ zero_le) hk
      exact hle.trans (le_add_of_nonneg_right zero_le)
    · rw [indicator_of_mem (show x ∈ badSingletonLengthDiagonalEvent μ C from ⟨hx.1, hd⟩)]
      exact (hB _ hk).trans (le_add_of_nonneg_left zero_le)
  · have hz (σ : Matching n) : (scoreStableSingletonAnchorEvent μ σ).indicator
        (fun _ ↦ g σ.support.card) x = 0 :=
      indicator_of_notMem (fun h ↦ he ⟨σ, h⟩) _
    simp only [hz, Finset.sum_const_zero, zero_le]
theorem lintegral_profileSingletonAnchorLengthWeight_le_of_lengthEvents (n : ℕ)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) (g : ℕ → ℝ≥0∞)
    {B : ℝ≥0∞} (hB : ∀ k ∈ Finset.Icc 2 n, g k ≤ B)
    {a : ℕ → ℝ≥0∞}
    (hgood : ∀ (μ : Matching n) k, k ∈ Finset.Icc 2 n →
      continuousScoreLaw n (scoreStableSingletonLengthEvent μ C k) ≤
        continuousScoreLaw n {x | IsScoreStable x μ} * a k) :
    (∫⁻ p, profileSingletonAnchorLengthWeight p g ∂(uniformProfile n).toMeasure) ≤
      ENNReal.ofReal (expectedNumStableMatchings n) * (∑ k ∈ Finset.Icc 2 n, g k * a k) +
        B * ∑ μ : Matching n, continuousScoreLaw n (badSingletonLengthDiagonalEvent μ C) := by
  classical
  rw [lintegral_profileSingletonAnchorLengthWeight_eq_sum_scoreStableSingletonAnchorEvent]
  let m (μ : Matching n) := continuousScoreLaw n {x | IsScoreStable x μ}
  let e (μ : Matching n) := continuousScoreLaw n (badSingletonLengthDiagonalEvent μ C)
  have hm (μ : Matching n) :
      (∑ σ : Matching n, g σ.support.card *
        continuousScoreLaw n (scoreStableSingletonAnchorEvent μ σ)) ≤
        m μ * (∑ k ∈ Finset.Icc 2 n, g k * a k) + B * e μ := by
    let f (σ : Matching n) := (scoreStableSingletonAnchorEvent μ σ).indicator
      (fun _ ↦ g σ.support.card)
    let q (k : ℕ) := (scoreStableSingletonLengthEvent μ C k).indicator (fun _ ↦ g k)
    let v := (badSingletonLengthDiagonalEvent μ C).indicator (fun _ ↦ B)
    have hf (σ : Matching n) : Measurable (f σ) :=
      measurable_const.indicator (measurableSet_scoreStableSingletonAnchorEvent μ σ)
    have hq (k : ℕ) : Measurable (q k) :=
      measurable_const.indicator (measurableSet_scoreStableSingletonLengthEvent μ hC k)
    calc
      _ = ∫⁻ x, ∑ σ : Matching n, f σ x ∂continuousScoreLaw n := by
        rw [lintegral_finsetSum _ (fun σ _ ↦ hf σ)]
        exact Finset.sum_congr rfl fun σ _ ↦
          (lintegral_indicator_const (measurableSet_scoreStableSingletonAnchorEvent μ σ) _).symm
      _ ≤ ∫⁻ x, (∑ k ∈ Finset.Icc 2 n, q k x) + v x ∂continuousScoreLaw n :=
        lintegral_mono (sum_singletonAnchor_indicators_le μ C g hB)
      _ = (∑ k ∈ Finset.Icc 2 n, g k *
          continuousScoreLaw n (scoreStableSingletonLengthEvent μ C k)) + B * e μ := by
        rw [lintegral_add_left (Finset.measurable_sum _ fun k _ ↦ hq k),
          lintegral_finsetSum _ (fun k _ ↦ hq k)]
        congr 1
        · exact Finset.sum_congr rfl fun k _ ↦
            lintegral_indicator_const (measurableSet_scoreStableSingletonLengthEvent μ hC k) _
        · exact lintegral_indicator_const (measurableSet_badSingletonLengthDiagonalEvent μ hC) _
      _ ≤ _ := by
        rw [Finset.mul_sum]
        refine add_le_add (Finset.sum_le_sum fun k hk ↦ ?_) le_rfl
        exact (mul_le_mul_right (hgood μ k hk) _).trans_eq (by ac_rfl)
  refine (Finset.sum_le_sum fun μ _ ↦ hm μ).trans_eq ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  unfold m e
  rw [sum_measure_scoreStable_eq_expected]
private noncomputable def singletonLengthBudget (n : ℕ) : ℝ :=
  3 * (n : ℝ) ^ (-3 / 4 : ℝ) + 24 / (n : ℝ)
private noncomputable def singletonLengthEnvelope (n k : ℕ) : ℝ :=
  Real.exp 5 * singletonLengthGaussian n k * (singletonLengthBudget n / (k : ℝ) + 24 / (n : ℝ))
theorem singletonLengthEnvelope_nonneg (n k : ℕ) : 0 ≤ singletonLengthEnvelope n k := by
  unfold singletonLengthEnvelope singletonLengthBudget singletonLengthGaussian
  positivity
theorem eventually_measure_scoreStableSingletonLengthEvent_le :
    ∀ᶠ n : ℕ in atTop, ∀ (μ : Matching n) k, k ∈ Finset.Icc 2 n →
      continuousScoreLaw n (scoreStableSingletonLengthEvent μ (singletonLengthGoodDiagonal n) k) ≤
        continuousScoreLaw n {x | IsScoreStable x μ} *
          ENNReal.ofReal (singletonLengthEnvelope n k) := by
  filter_upwards [eventually_coexposureSuccessorPerturbation_bounds,
    eventually_hasForwardReferenceDeficit_of_singletonLengthGoodDiagonal] with n hp hdef
  obtain ⟨hn, hη₀, hη, hA, hB, hδ⟩ := hp
  intro μ k hk
  let : MeasurableSpace (Option (Fin n)) := ⊤
  let : MeasurableSingletonClass (Option (Fin n)) := ⟨fun _ ↦ trivial⟩
  refine measure_scoreStable_diagonal_rankEvent_le μ
    (measurableSet_singletonLengthGoodDiagonal n) (fun _ h ↦ ⟨h.2.1, h.2.2.1⟩)
    {p | HasSoleForwardExposedLength p μ k} ?_
  filter_upwards [ae_diagonal_measureReal_soleForwardExposedLength_le hn μ hη₀ hη hA hB hδ]
    with d hd
  intro h
  have hsq : (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ) := h.2.2.2.2.1
  have hk₀ := (Finset.mem_Icc.mp hk).1
  have hk₁ := (Finset.mem_Icc.mp hk).2
  refine (hd h.1 h.2.1 h.2.2.1 _ (hdef d h) k hk₀ hk₁).trans ?_
  unfold singletonLengthEnvelope singletonLengthBudget singletonLengthGaussian
  gcongr
theorem eventually_lintegral_profileSingletonAnchorLengthWeight_le_gaussian :
    ∀ᶠ n : ℕ in atTop, ∀ (g : ℕ → ℝ) (B : ℝ),
      (∀ k, 0 ≤ g k) → (∀ k ∈ Finset.Icc 2 n, g k ≤ B) →
      (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))
        ∂(uniformProfile n).toMeasure) ≤
        ENNReal.ofReal (expectedNumStableMatchings n) *
          ENNReal.ofReal (∑ k ∈ Finset.Icc 2 n, g k * singletonLengthEnvelope n k) +
          ENNReal.ofReal B * ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ)) := by
  filter_upwards [eventually_measure_scoreStableSingletonLengthEvent_le,
    eventually_sum_measure_badSingletonLengthDiagonal_le] with n hgood hbad
  intro g B hg hB
  have hb := lintegral_profileSingletonAnchorLengthWeight_le_of_lengthEvents n
    (measurableSet_singletonLengthGoodDiagonal n) (fun k ↦ ENNReal.ofReal (g k))
    (fun k hk ↦ ENNReal.ofReal_le_ofReal (hB k hk)) hgood
  refine hb.trans ?_
  have hsum : (∑ k ∈ Finset.Icc 2 n, ENNReal.ofReal (g k) *
      ENNReal.ofReal (singletonLengthEnvelope n k)) =
      ENNReal.ofReal (∑ k ∈ Finset.Icc 2 n, g k * singletonLengthEnvelope n k) := by
    simp_rw [← ENNReal.ofReal_mul (hg _)]
    exact (ENNReal.ofReal_sum_of_nonneg fun k _ ↦
      mul_nonneg (hg k) (singletonLengthEnvelope_nonneg n k)).symm
  rw [hsum]
  exact add_le_add le_rfl (mul_le_mul_right hbad _)
end StepA2
end

-- RotationLengthCutoff
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal StepA2 Topology
namespace StepA2
end StepA2
end

-- RotationClockBand
section
open Filter MeasureTheory StableMarriage
open scoped ENNReal Topology
namespace StepA2
end StepA2
end

-- ScoreRotationHistory
section
open StableMarriage
open scoped Classical
namespace StepA2
variable {n : ℕ}
end StepA2
end

-- ScoreRotationBandCrossing
section
open StableMarriage
open scoped BigOperators
namespace StepA2
variable {n : ℕ}
end StepA2
end

-- DAUpperEndpoint
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
end StepA2
end

-- ParticipationClockMartingale
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace StepA2
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {ℱ : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
end StepA2
end

-- FinitePartitionClock
section
open MeasureTheory Set
open scoped Function
namespace StepA2
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
end StepA2
end

-- ScoreClockFiltration
section
open MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepA2
variable {n : ℕ}
end StepA2
end

-- ScoreRotationBranchTest
section
open MeasureTheory Set StableMarriage
open scoped Classical
namespace StepA2
variable {n : ℕ}
end StepA2
end

-- ScoreRotationClockBudget
section
open MeasureTheory Set StableMarriage
open scoped BigOperators Classical Function
namespace StepA2
variable {n : ℕ}
end StepA2
end

-- ScoreRotationClockMaximal
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology
namespace StepA2
variable {n : ℕ}
end StepA2
end

-- ScoreRotationLengthBudgets
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology
namespace StepA2
end StepA2
end

-- ScoreRotationBandAbundance
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology
namespace StepA2
end StepA2
end

-- ScoreRotationAnchorAbundance
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology
namespace StepA2
end StepA2
end

-- ScoreRotationNonTiny
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology
namespace StepA2
end StepA2
end

-- ScoreRotationAnchorProbability
section
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace StepA2
end StepA2
end

-- DAEndpointAsymptotics
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology StepA2
namespace StepA2
end StepA2
end

-- PivotMarkedCutoffBridge
section
open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
section IndependentRows
variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
  (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
  (out : ∀ i, Ω i → Option (Fin n)) (g : ∀ i, Fin n → Ω i → ℝ)
  [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
end IndependentRows
end StepA2
end

-- PivotSupportMassTail
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology
namespace StepA2
end StepA2
end

-- PivotForwardIncrementTail
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
end StepA2
end

-- PivotEligibleAbundance
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
end StepA2
end

-- PivotAggregateMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA2
variable {n : ℕ}
end StepA2
end

-- PivotDecorationRevealInvariance
section
open MeasureTheory Set StableMarriage
namespace StepA2
variable {n : ℕ} {μ ρ σ : Matching n} {x y : ScoreProfile n}
  {flag : OffDiagonalCellIndex n → Bool}
private structure SameReverseReveal (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x y : ScoreProfile n) : Prop where
  diagonal : (splitScorePairs μ x).1 = (splitScorePairs μ y).1
  observed : forwardRevealWithColumns flag (splitScorePairs μ x).2 =
    forwardRevealWithColumns flag (splitScorePairs μ y).2
theorem SameReverseReveal.symm (h : SameReverseReveal μ flag x y) :
    SameReverseReveal μ flag y x := ⟨h.diagonal.symm, h.observed.symm⟩
end StepA2
end

-- PivotLaterRevealReplay
section
open MeasureTheory Set StableMarriage
namespace StepA2
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
end StepA2
end

-- PivotComparableCentered
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
namespace PivotCountParameters
variable {n : ℕ}
end PivotCountParameters
end StepA2
end

-- PivotTwoCycleForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA2
end StepA2
end

-- LogarithmicCutoffs
section
open Filter
open scoped Topology BigOperators
namespace StepA2
end StepA2
end

-- PivotVarianceClosure
section
open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators ENNReal Topology
namespace StepA2
namespace PivotCountParameters
variable {n : ℕ}
end PivotCountParameters
variable {n : ℕ}
namespace PivotCountParameters
end PivotCountParameters
end StepA2
end

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 30000 in
theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H1_R1.H2 :=
  @StepA2.eventually_lintegral_profileSingletonAnchorLengthWeight_le_gaussian
