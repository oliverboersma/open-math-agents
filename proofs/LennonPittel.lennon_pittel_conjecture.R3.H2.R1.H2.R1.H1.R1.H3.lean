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
namespace StepA3
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
end StepA3
end

-- BoundedProductChernoff
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA3
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
end StepA3
end

-- IidScoreRanks
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace StepA3
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
end StepA3
end

-- MarkedCounting
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
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
end StepA3
end

-- ScoreRanks
section
open Function MeasureTheory Set
namespace StepA3
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
end StepA3
end

-- ContinuousScoreBridge
section
open scoped BigOperators ENNReal StepA3
open MeasureTheory Set
namespace StepA3
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
end StepA3
end

-- CoexposureGoodScores
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal StepA3
namespace StepA3
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
private def badStableSpouseScores (n : ℕ) (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ ¬GoodSpouseScores x μ}
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
theorem badCoexposureScores_ae_eq_iUnion (n : ℕ) :
    (goodCoexposureScores n)ᶜ =ᵐ[continuousScoreLaw n]
      ⋃ μ : Matching n, badStableSpouseScores n μ := by
  filter_upwards [ae_injective_rows n, ae_unitOpen_scores n] with x hrow hopen
  apply propext
  constructor
  · intro hbad
    have hfail : ¬∀ μ, IsStable (profileOfScores x) μ → GoodSpouseScores x μ :=
      fun hgood ↦ hbad ⟨hrow, hopen, hgood⟩
    obtain ⟨μ, hμ⟩ := not_forall.mp hfail
    obtain ⟨hs, hb⟩ := Classical.not_imp.mp hμ
    exact Set.mem_iUnion.mpr ⟨μ, (isStable_profileOfScores_iff hrow μ).mp hs, hb⟩
  · intro hbad hgood
    obtain ⟨μ, hs, hb⟩ := Set.mem_iUnion.mp hbad
    exact hb (hgood.2.2 μ ((isStable_profileOfScores_iff hrow μ).mpr hs))
theorem measure_badCoexposureScores_le_sum (n : ℕ) :
    continuousScoreLaw n (goodCoexposureScores n)ᶜ ≤
      ∑ μ : Matching n, continuousScoreLaw n (badStableSpouseScores n μ) :=
  (measure_congr (badCoexposureScores_ae_eq_iUnion n)).le.trans
    (measure_iUnion_fintype_le _ _)
end StepA3
end

-- CoexposureScoreEstimates
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepA3
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
end StepA3
end

-- PittelSimplexRadial
section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace StepA3
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
end StepA3
end

-- PittelSimplexMoments
section
open Filter MeasureTheory Set
open scoped ENNReal BigOperators Topology
namespace StepA3
private noncomputable def pittelAngularSquareScore {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (n : ℝ) * ∑ i, w i ^ 2
section Moments
variable {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
variable (hμ : ∀ᵐ w ∂μ, ∀ i, w i ∈ Icc (0 : ℝ) 1)
variable (hmoment : ∀ a : Fin n → ℕ, (∫ w, ∏ i, w i ^ a i ∂μ) =
  (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
    ((n - 1 + ∑ i, a i).factorial : ℝ))
end Moments
end StepA3
end

-- ExponentialSpouseSquareTail
section
open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
namespace StepA3
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
end StepA3
end

-- ExponentialSpouseAngles
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace StepA3
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
end StepA3
end

-- CoexposureScoreRow
section
open Set
open scoped BigOperators
namespace StepA3
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
section SuccessorMass
open MeasureTheory
open scoped ENNReal
end SuccessorMass
end StepA3
end

-- ExposedRotations
section
open StableMarriage
namespace StepA3
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
end StepA3
end

-- CoexposureScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
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
end StepA3
end

-- CoexposureSpouseMarginal
section
open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
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
theorem tendsto_sum_measure_badMaleSpouseScores_zero_of_mean_upper {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ᶠ n : ℕ in atTop,
      expectedNumStableMatchings n ≤ C * ((n : ℝ) * Real.log n)) :
    Tendsto (fun n : ℕ ↦ ∑ μ : Matching n, continuousScoreLaw n (badMaleSpouseScores μ))
      atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (8 * C / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_apply, ← div_eq_mul_inv, mul_zero] using
      ENNReal.tendsto_ofReal ((tendsto_inv_atTop_zero.comp hcast).const_mul (8 * C))
  refine tendsto_const_nhds.squeeze' ht (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ), hmean] with n hn hm
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn'
  have hlog : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos hp).trans (by linarith)
  have hm' : expectedNumStableMatchings n ≤ C * (n : ℝ) ^ 2 := by
    refine hm.trans ?_
    rw [sq]
    gcongr
  refine (sum_measure_badMaleSpouseScores_le (zero_lt_one.trans_le hn)).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (8 / (n : ℝ) ^ 7) * (C * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hm' (by positivity)
    _ = (8 * C / (n : ℝ)) / ((n : ℝ) ^ 4) := by field_simp
    _ ≤ _ := div_le_self (by positivity) (one_le_pow₀ hn')
end StepA3
end

-- CoexposureSpouseShells
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepA3
private def spouseVectorTotal {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  ∑ i, y i
private theorem measurable_spouseVectorTotal (n : ℕ) :
    Measurable (@spouseVectorTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
private def largeRelativeSpouseScoreSet (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ 2 ≤ spouseVectorTotal y ∧ spouseVectorTotal y ≤ n ∧
    ∃ i, 12 * Real.log n / n < y i / spouseVectorTotal y}
private def smallSpouseScoreSet (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ spouseVectorTotal y < 2}
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
theorem measurableSet_smallSpouseScoreSet (n : ℕ) :
    MeasurableSet (smallSpouseScoreSet n) := by
  unfold smallSpouseScoreSet
  rw [ofPred_and]
  exact (measurableSet_nonnegativeSpouseScores n).inter
    (measurableSet_lt (measurable_spouseVectorTotal n) measurable_const)
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
theorem factorial_mul_lintegral_smallSpouseScore_le {n : ℕ} (hn : 0 < n)
    {f : (Fin n → ℝ) → ℝ≥0∞}
    (hf₀ : ∀ y ∈ smallSpouseScoreSet n, spouseVectorTotal y ≤ 1 / 2 → f y ≤ 1)
    (hf₁ : ∀ y ∈ smallSpouseScoreSet n, 1 / 2 ≤ spouseVectorTotal y →
      f y ≤ ENNReal.ofReal (Real.exp (spouseVectorTotal y) *
        ((1 - Real.exp (-spouseVectorTotal y)) / spouseVectorTotal y) ^ n)) :
    (n.factorial : ℝ≥0∞) * (∫⁻ y in smallSpouseScoreSet n, f y) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) +
        ENNReal.ofReal ((2 * (n : ℝ) + 1) * Real.exp 4 * (1 - Real.exp (-2)) ^ n) := by
  let A := smallSpouseScoreSet n ∩ scoreSimplex n (1 / 2)
  have hsmall := measurableSet_smallSpouseScoreSet n
  have hA : MeasurableSet A := hsmall.inter (measurableSet_scoreSimplex _ _)
  have hnear : (n.factorial : ℝ≥0∞) * (∫⁻ y in A, f y) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    have hbound := lintegral_le_const_mul_volume hA (fun y hy ↦ hf₀ y hy.1 hy.2.2)
    have hvol : volume A ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n / (n.factorial : ℝ)) := by
      rw [← volume_scoreSimplex n (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact measure_mono inter_subset_right
    calc
      _ ≤ (n.factorial : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n / (n.factorial : ℝ)) := by
        have h := (by simpa only [one_mul] using hbound :
          (∫⁻ y in A, f y) ≤ volume A)
        exact mul_le_mul_right (h.trans hvol) _
      _ = _ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]
  let l (j : Fin (2 * n + 1)) : ℝ := 1 / 2 + j.val / (n : ℝ)
  let S (j : Fin (2 * n + 1)) : Set (Fin n → ℝ) :=
    smallSpouseScoreSet n ∩ {y | y ∈ scoreSimplex n (l j + 1 / (n : ℝ)) ∧
      l j ≤ spouseVectorTotal y}
  have hS (j : Fin (2 * n + 1)) : MeasurableSet (S j) := by
    refine hsmall.inter ?_
    rw [ofPred_and]
    exact (measurableSet_scoreSimplex _ _).inter
      (measurableSet_le measurable_const (measurable_spouseVectorTotal n))
  have hcover : smallSpouseScoreSet n ⊆ A ∪ ⋃ j, S j := by
    intro y hy
    by_cases ht : spouseVectorTotal y ≤ 1 / 2
    · exact Or.inl ⟨hy, hy.1, ht⟩
    · have hs : (spouseVectorTotal y - 1 / 2) * (n : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
        push_cast
        exact mul_le_mul_of_nonneg_right (by linarith [hy.2]) (Nat.cast_nonneg n)
      obtain ⟨j, hj₁, hj₂⟩ := exists_shell_index hn (le_of_not_ge ht) hs
      exact Or.inr (mem_iUnion.mpr ⟨j, hy, ⟨hy.1, hj₂.trans_eq (by
        dsimp only [l]
        ring)⟩, hj₁⟩)
  let q : ℝ := 1 - Real.exp (-2)
  have hq₀ : 0 ≤ q := by
    dsimp [q]
    linarith [Real.exp_le_one_iff.mpr (by norm_num : (-2 : ℝ) ≤ 0)]
  let c := Real.exp 4 * q ^ n
  have hlocal (j : Fin (2 * n + 1)) :
      (∫⁻ y in S j, f y) ≤ ENNReal.ofReal (c / (n.factorial : ℝ)) := by
    have hlhalf : 1 / 2 ≤ l j := le_add_of_nonneg_right (by positivity)
    have hl : 0 < l j := by linarith
    have hR : 0 ≤ l j + 1 / (n : ℝ) := by positivity
    have hV : volume (S j) ≤
        ENNReal.ofReal ((l j + 1 / (n : ℝ)) ^ n / (n.factorial : ℝ)) := by
      rw [← volume_scoreSimplex n hR]
      exact measure_mono fun _ hy ↦ hy.2.1
    have hdens (y : Fin n → ℝ) (hy : y ∈ S j) :
        f y ≤ ENNReal.ofReal (Real.exp 2 * q ^ n / spouseVectorTotal y ^ n) := by
      have hs : 1 / 2 ≤ spouseVectorTotal y := hlhalf.trans hy.2.2
      refine (hf₁ y hy.1 hs).trans (ENNReal.ofReal_le_ofReal ?_)
      have hs₀ : 0 ≤ 1 - Real.exp (-spouseVectorTotal y) := by
        linarith [Real.exp_le_one_iff.mpr (by linarith : -spouseVectorTotal y ≤ 0)]
      have hsq : 1 - Real.exp (-spouseVectorTotal y) ≤ q :=
        sub_le_sub_left (Real.exp_le_exp.mpr (by linarith [hy.1.2])) 1
      rw [div_pow, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (Real.exp_le_exp.mpr hy.1.2.le)
          (pow_le_pow_left₀ hs₀ hsq _) (pow_nonneg hs₀ _) (Real.exp_pos _).le)
        (pow_nonneg (by linarith) _)
    refine (lintegral_spouseShell_le (hS j) hl (by positivity) (fun _ hy ↦ hy.2.2)
      hV hdens).trans (ENNReal.ofReal_le_ofReal ?_)
    have hratio := thinShell_ratio_pow_le hn (by norm_num : (0 : ℝ) < 1 / 2) hlhalf
      (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at hratio
    have hcoef : Real.exp 2 * q ^ n * Real.exp 2 = c := by
      dsimp only [c]
      rw [show Real.exp 4 = Real.exp 2 * Real.exp 2 by rw [← Real.exp_add]; norm_num]
      ring
    rw [← hcoef]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using hratio) (by positivity)) (Nat.cast_nonneg _)
  have hshells : (n.factorial : ℝ≥0∞) * (∫⁻ y in ⋃ j, S j, f y) ≤
      ENNReal.ofReal ((2 * (n : ℝ) + 1) * Real.exp 4 * q ^ n) := by
    calc
      _ ≤ (n.factorial : ℝ≥0∞) * ∑ j : Fin (2 * n + 1), ∫⁻ y in S j, f y := by
        exact mul_le_mul_right (by simpa [tsum_fintype] using
          (lintegral_iUnion_le S f : (∫⁻ y in ⋃ j, S j, f y) ≤
            ∑' j, ∫⁻ y in S j, f y)) _
      _ ≤ (n.factorial : ℝ≥0∞) * ∑ _ : Fin (2 * n + 1),
          ENNReal.ofReal (c / (n.factorial : ℝ)) := by
        gcongr with j _
        exact hlocal j
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [← ENNReal.ofReal_natCast]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        dsimp only [c]
        field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]
  have hUnion := (lintegral_mono_set hcover).trans
    (lintegral_union_le (μ := volume) f A (⋃ j, S j))
  exact (mul_le_mul_right hUnion _).trans (by rw [mul_add]; exact add_le_add hnear hshells)
theorem tendsto_factorial_mul_lintegral_largeRelativeSpouseScore_zero
    (f : ∀ n : ℕ, (Fin n → ℝ) → ℝ≥0∞)
    (hf : ∀ᶠ n in atTop, ∀ y ∈ largeRelativeSpouseScoreSet n,
      f n y ≤ ENNReal.ofReal (Real.exp 2 / spouseVectorTotal y ^ n)) :
    Tendsto (fun n ↦ (n.factorial : ℝ≥0∞) *
      (∫⁻ y in largeRelativeSpouseScoreSet n, f n y)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ ↦ 12 * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop one_pos).tendsto_div_nhds_zero.comp hcast
    simpa only [Function.comp_apply, Real.rpow_one, ← mul_div_assoc, mul_zero] using
      h.const_mul (12 : ℝ)
  have hcut : ∀ᶠ n : ℕ in atTop, 12 * Real.log (n : ℝ) / (n : ℝ) ≤ 1 :=
    ((tendsto_order.mp hlog).2 1 zero_lt_one).mono fun _ h ↦ h.le
  have ht : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (2 * Real.exp (5 / 2) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_apply, ← div_eq_mul_inv, mul_zero] using
      ENNReal.tendsto_ofReal ((tendsto_inv_atTop_zero.comp hcast).const_mul
        (2 * Real.exp (5 / 2)))
  refine tendsto_const_nhds.squeeze' ht (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ), hcut, hf] with n hn hc h
  refine (factorial_mul_lintegral_largeRelativeSpouseScore_le
    (zero_lt_one.trans_le hn) hc h).trans (ENNReal.ofReal_le_ofReal ?_)
  have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx₀ : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hx
  apply (div_le_div_iff₀ (pow_pos hx₀ _) hx₀).2
  have hxx : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hx
  calc
    _ ≤ (2 * (n : ℝ) ^ 2) * n * Real.exp (5 / 2) * n := by
      gcongr
      linarith
    _ = 2 * Real.exp (5 / 2) * (n : ℝ) ^ 4 := by ring
    _ ≤ _ := by
      gcongr
      norm_num
theorem tendsto_factorial_mul_lintegral_smallSpouseScore_zero
    (f : ∀ n : ℕ, (Fin n → ℝ) → ℝ≥0∞)
    (hf₀ : ∀ᶠ n in atTop, ∀ y ∈ smallSpouseScoreSet n,
      spouseVectorTotal y ≤ 1 / 2 → f n y ≤ 1)
    (hf₁ : ∀ᶠ n in atTop, ∀ y ∈ smallSpouseScoreSet n, 1 / 2 ≤ spouseVectorTotal y →
      f n y ≤ ENNReal.ofReal (Real.exp (spouseVectorTotal y) *
        ((1 - Real.exp (-spouseVectorTotal y)) / spouseVectorTotal y) ^ n)) :
    Tendsto (fun n ↦ (n.factorial : ℝ≥0∞) *
      (∫⁻ y in smallSpouseScoreSet n, f n y)) atTop (𝓝 0) := by
  let q : ℝ := 1 - Real.exp (-2)
  have hq₀ : 0 ≤ q :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  have hq₁ : q < 1 := sub_lt_self _ (Real.exp_pos _)
  have hhalf : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁
  have hngeom := tendsto_self_mul_const_pow_of_lt_one hq₀ hq₁
  have hterm : Tendsto (fun n : ℕ ↦ (2 * (n : ℝ) + 1) * Real.exp 4 * q ^ n)
      atTop (𝓝 0) := by
    have h := ((hngeom.const_mul (2 : ℝ)).add hgeom).const_mul (Real.exp 4)
    rw [mul_zero, zero_add, mul_zero] at h
    refine h.congr fun n ↦ ?_
    ring
  have ht : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) +
      ENNReal.ofReal ((2 * (n : ℝ) + 1) * Real.exp 4 * q ^ n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, zero_add] using
      (ENNReal.tendsto_ofReal hhalf).add (ENNReal.tendsto_ofReal hterm)
  refine tendsto_const_nhds.squeeze' ht (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ), hf₀, hf₁] with n hn h₀ h₁
  exact factorial_mul_lintegral_smallSpouseScore_le (zero_lt_one.trans_le hn) h₀ h₁
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
theorem tendsto_sum_stable_smallSpouseScore_zero :
    Tendsto (fun n : ℕ ↦ ∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ smallSpouseScoreSet n})
      atTop (𝓝 0) := by
  simp_rw [sum_stable_femaleSpouse_eq_factorial_mul (measurableSet_smallSpouseScoreSet _)]
  apply tendsto_factorial_mul_lintegral_smallSpouseScore_zero
  · exact Eventually.of_forall fun n y _ _ ↦ by
      by_cases hy : y ∈ spouseScoreCube n
      · rw [maskedFemaleStabilityDensity, indicator_of_mem hy]
        exact femaleSpouseStabilityDensity_le_one y (fun j ↦ hy j (mem_univ j))
      · simp [maskedFemaleStabilityDensity, indicator_of_notMem hy]
  · exact Eventually.of_forall fun n y _ hs ↦ by
      by_cases hy : y ∈ spouseScoreCube n
      · have hcube (j : Fin n) : y j ∈ Icc (0 : ℝ) 1 := hy j (mem_univ j)
        change 1 / 2 ≤ ∑ j, y j at hs
        rw [maskedFemaleStabilityDensity, indicator_of_mem hy,
          femaleSpouseStabilityDensity_eq_ofReal_prod hcube]
        apply ENNReal.ofReal_le_ofReal
        simpa only [spouseVectorTotal, Fintype.card_fin] using
          scoreRowMass_prod_le_finite_exp y hcube (by linarith [hs])
      · simp [maskedFemaleStabilityDensity, indicator_of_notMem hy]
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
theorem tendsto_sum_stable_largeRelativeSpouseScore_zero :
    Tendsto (fun n : ℕ ↦ ∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ largeRelativeSpouseScoreSet n})
      atTop (𝓝 0) := by
  simp_rw [sum_stable_femaleSpouse_eq_factorial_mul
    (measurableSet_largeRelativeSpouseScoreSet _)]
  apply tendsto_factorial_mul_lintegral_largeRelativeSpouseScore_zero
  exact Eventually.of_forall fun _ _ ↦ maskedFemaleStabilityDensity_le_of_largeRelativeSpouseScore
end StepA3
end

-- PittelMeanTail
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
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
end StepA3
end

-- MarkedSpouseAngleComparison
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
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
end StepA3
end

-- ScoreSideSwap
section
open MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepA3
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
theorem isScoreBlockingPair_swapScoreSides_iff {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (m w : Fin n) :
    IsScoreBlockingPair (swapScoreSides x) μ.symm w m ↔ IsScoreBlockingPair x μ m w := by
  have hne : μ.symm w ≠ m ↔ μ m ≠ w := by
    constructor
    · intro h hmw
      exact h (by rw [← hmw, μ.symm_apply_apply])
    · intro h hwm
      exact h (by rw [← hwm, μ.apply_symm_apply])
  simp only [IsScoreBlockingPair, swapScoreSides, Sum.swap_inl, Sum.swap_inr,
    Equiv.symm_symm, hne, and_comm (a := x (.inr w) m < x (.inr w) (μ.symm w))]
theorem isScoreStable_swapScoreSides_iff {n : ℕ} (x : ScoreProfile n) (μ : Matching n) :
    IsScoreStable (swapScoreSides x) μ.symm ↔ IsScoreStable x μ := by
  constructor
  · intro h m w
    exact mt (isScoreBlockingPair_swapScoreSides_iff x μ m w).mpr (h w m)
  · intro h w m
    exact mt (isScoreBlockingPair_swapScoreSides_iff x μ m w).mp (h m w)
theorem femaleSpouseByHusband_swapScoreSides {n : ℕ} (x : ScoreProfile n) (μ : Matching n) :
    femaleSpouseByHusband μ.symm (swapScoreSides x) =
      (fun i ↦ maleSpouseScore x μ i) ∘ μ.symm := by
  funext i
  rfl
theorem scoreStable_maleSpouseStatistic_measure_eq_female {n : ℕ} (μ : Matching n)
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S)
    (hinv : ∀ (v : Fin n → ℝ) (e : Equiv.Perm (Fin n)), v ∘ e ∈ S ↔ v ∈ S) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ (fun i ↦ maleSpouseScore x μ i) ∈ S} =
      continuousScoreLaw n {x | IsScoreStable x μ.symm ∧ femaleSpouseByHusband μ.symm x ∈ S} := by
  let T : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ.symm ∧ femaleSpouseByHusband μ.symm x ∈ S}
  have hT : MeasurableSet T := (measurableSet_isScoreStable μ.symm).inter
    (hS.preimage (measurable_pi_iff.2 fun i ↦ measurable_femaleSpouseScore μ.symm (μ.symm i)))
  have hpre : swapScoreSides ⁻¹' T =
      {x | IsScoreStable x μ ∧ (fun i ↦ maleSpouseScore x μ i) ∈ S} := by
    ext x
    change IsScoreStable (swapScoreSides x) μ.symm ∧
      femaleSpouseByHusband μ.symm (swapScoreSides x) ∈ S ↔ _
    rw [isScoreStable_swapScoreSides_iff, femaleSpouseByHusband_swapScoreSides, hinv]
    rfl
  rw [← hpre]
  exact (measurePreserving_swapScoreSides n).measure_preimage hT.nullMeasurableSet
theorem spouseAngle_comp_equiv {n : ℕ} (v : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    spouseAngle (v ∘ e) = spouseAngle v ∘ e := by
  funext i
  change v (e i) / (∑ j, v (e j)) = v (e i) / (∑ j, v j)
  rw [Equiv.sum_comp e v]
theorem pittelAngularSquareScore_spouseAngle_comp_equiv {n : ℕ} (v : Fin n → ℝ)
    (e : Equiv.Perm (Fin n)) :
    pittelAngularSquareScore (spouseAngle (v ∘ e)) = pittelAngularSquareScore (spouseAngle v) := by
  rw [spouseAngle_comp_equiv]
  unfold pittelAngularSquareScore
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp e (fun i ↦ spouseAngle v i ^ 2)]
end StepA3
end

-- StableMaleSpouseRowLaw
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
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
private theorem scoreRowMass_erase_le_two_div {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) (i : Fin n) :
    scoreRowMass (Finset.univ.erase i) y 0 1 ≤ 2 / ∑ j, y j := by
  let Y := ∑ j, y j
  have hY : 0 < Y := by linarith
  have hrate : 0 < Y - 1 := by linarith
  have hsum := Finset.sum_erase_add (s := Finset.univ) y (Finset.mem_univ i)
  have herase : Y - 1 ≤ ∑ j ∈ Finset.univ.erase i, y j := by
    linarith only [hsum, (hy i).2]
  calc
    _ ≤ 1 / (Y - 1) := by
      simpa using scoreRowMass_le_exp_tail (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2)
        hrate herase (a := 0) (b := 1) le_rfl zero_le_one le_rfl
    _ ≤ 2 / Y := by
      apply (div_le_div_iff₀ hrate hY).mpr
      linarith
private theorem one_div_eight_mul_le_stableMaleSpouseRowLaw_goodInterval {n : ℕ}
    (y : Fin n → ℝ) (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) (i : Fin n) :
    ENNReal.ofReal (1 / (8 * ∑ j, y j)) ≤
      stableMaleSpouseRowLaw y i (Ioc (1 / (4 * ∑ j, y j)) (1 / (2 * ∑ j, y j))) := by
  let Y := ∑ j, y j
  let a := 1 / (4 * Y)
  let b := 1 / (2 * Y)
  have hY : 0 < Y := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : b ≤ 1 := (div_le_iff₀ (by positivity : 0 < 2 * Y)).mpr (by linarith)
  have hle : ∑ j ∈ Finset.univ.erase i, y j ≤ Y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ ↦ (hy j).1
  have hsub : Ioc a b ⊆ Icc (0 : ℝ) 1 :=
    fun _ ht ↦ ⟨ha.trans ht.1.le, ht.2.trans hb⟩
  have hvol : unitScoreLaw (Ioc a b) = ENNReal.ofReal (b - a) := by
    rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr hsub, Real.volume_Ioc]
  have hhalf : (1 / 2 : ℝ) * (b - a) = 1 / (8 * Y) := by
    dsimp [a, b]
    field_simp
    norm_num
  change ENNReal.ofReal (1 / (8 * Y)) ≤ stableMaleSpouseRowLaw y i (Ioc a b)
  rw [← hhalf, ENNReal.ofReal_mul (by norm_num), ← hvol, stableMaleSpouseRowLaw,
    withDensity_apply _ measurableSet_Ioc]
  have heq : ENNReal.ofReal (1 / 2 : ℝ) * unitScoreLaw (Ioc a b) =
      ∫⁻ _t in Ioc a b, ENNReal.ofReal (1 / 2 : ℝ) ∂unitScoreLaw := by
    rw [lintegral_const, Measure.restrict_apply_univ]
  rw [heq]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := unitScoreLaw)
    (measurableSet_Ioc : MeasurableSet (Ioc a b))] with t ht
  have ht0 : 0 ≤ t := ha.trans ht.1.le
  have hprod : t * (∑ j ∈ Finset.univ.erase i, y j) ≤ 1 / 2 := calc
    _ ≤ t * Y := mul_le_mul_of_nonneg_left hle ht0
    _ ≤ b * Y := mul_le_mul_of_nonneg_right ht.2 hY.le
    _ = _ := by
      dsimp [b]
      field_simp
  apply ENNReal.ofReal_le_ofReal
  exact (by linarith : (1 / 2 : ℝ) ≤ 1 - t * ∑ j ∈ Finset.univ.erase i, y j).trans
    (one_sub_sum_le_scoreRowKernel (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2)
      ⟨ht0, ht.2.trans hb⟩)
theorem normalizedStableMaleSpouseRowLaw_goodInterval_ge {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) (i : Fin n) :
    ENNReal.ofReal (1 / 16 : ℝ) ≤
      normalizedStableMaleSpouseRowLaw y i
        (Ioc (1 / (4 * ∑ j, y j)) (1 / (2 * ∑ j, y j))) := by
  let Y := ∑ j, y j
  let A := Ioc (1 / (4 * Y)) (1 / (2 * Y))
  let M := stableMaleSpouseRowLaw y i univ
  have := stableMaleSpouseRowLaw_isFiniteMeasure y hy i
  have hM₀ : M ≠ 0 := (stableMaleSpouseRowLaw_univ_pos y hy hs i).ne'
  have hMtop : M ≠ ⊤ := measure_ne_top _ _
  have hbound : ENNReal.ofReal (1 / 16 : ℝ) * M ≤ stableMaleSpouseRowLaw y i A := calc
    _ ≤ ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (2 / Y) := by
      apply mul_le_mul_right _ _
      rw [show M = _ from stableMaleSpouseRowLaw_univ y hy i]
      exact ENNReal.ofReal_le_ofReal (scoreRowMass_erase_le_two_div y hy hs i)
    _ = ENNReal.ofReal (1 / (8 * Y)) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    _ ≤ _ := one_div_eight_mul_le_stableMaleSpouseRowLaw_goodInterval y hy hs i
  calc
    _ = ENNReal.ofReal (1 / 16 : ℝ) * (M⁻¹ * M) := by
      rw [ENNReal.inv_mul_cancel hM₀ hMtop, mul_one]
    _ = M⁻¹ * (ENNReal.ofReal (1 / 16 : ℝ) * M) := by ac_rfl
    _ ≤ M⁻¹ * stableMaleSpouseRowLaw y i A := mul_le_mul_right hbound _
    _ = _ := by rw [normalizedStableMaleSpouseRowLaw, Measure.smul_apply, smul_eq_mul]
end StepA3
end

-- IndependentFlagLowerTail
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA3
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
open scoped Classical in
theorem measure_pi_flagCount_lt_le {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (A : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i))
    (hp : ∀ i, ENNReal.ofReal (1 / 16) ≤ ν i (A i)) :
    (Measure.pi ν) {x | (∑ i, if x i ∈ A i then (1 : ℝ) else 0) < (Fintype.card ι : ℝ) / 32} ≤
      ENNReal.ofReal (Real.exp (-(Fintype.card ι : ℝ) / 128)) := by
  refine (measure_pi_flagCount_lt_le_exp ν A hA (1 / 16) _ (by norm_num) hp).trans ?_
  have he : Real.exp (-1) ≤ 3 / 8 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
    linarith only [Real.exp_one_gt_d9]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  linarith only [mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α := ℝ) (Fintype.card ι))]
end StepA3
end

-- FiniteProductDensity
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA3
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
end StepA3
end

-- SmallSpouseTotalLog
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepA3
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
end StepA3
end

-- MeanUpperBound
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepA3
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
end StepA3
end

-- PivotSpouseProductLower
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
private def maleSpouseTotal {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ i, maleSpouseScore x μ i
private def lowSpouseProductVectorSet (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | 2 ≤ spouseVectorTotal z.2 ∧
    spouseVectorTotal z.1 * spouseVectorTotal z.2 < (n : ℝ) / 128}
theorem measurableSet_lowSpouseProductVectorSet (n : ℕ) :
    MeasurableSet (lowSpouseProductVectorSet n) := by
  have h : Measurable (@spouseVectorTotal n) :=
    Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  exact (measurableSet_le measurable_const (h.comp measurable_snd)).inter
    (measurableSet_lt ((h.comp measurable_fst).mul (h.comp measurable_snd)) measurable_const)
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
open scoped Classical in
theorem flagCount_lt_of_spouseProduct_lt {n : ℕ} {x : Fin n → ℝ} {Y : ℝ} {A : Set ℝ}
    (hY : 0 < Y) (hA : A ⊆ Ioi (1 / (4 * Y))) (hx : ∀ i, 0 ≤ x i)
    (hbad : spouseVectorTotal x * Y < (n : ℝ) / 128) :
    (∑ i, if x i ∈ A then (1 : ℝ) else 0) < (n : ℝ) / 32 := by
  have h₁ (i : Fin n) : (if x i ∈ A then (1 : ℝ) else 0) ≤ 4 * Y * x i := by
    by_cases hi : x i ∈ A
    · rw [if_pos hi]
      have hl : 1 / (4 * Y) < x i := hA hi
      have h := ((div_lt_iff₀ (by positivity : 0 < 4 * Y)).mp hl).le
      simpa only [mul_comm (x i)] using h
    · rw [if_neg hi]
      exact mul_nonneg (by positivity) (hx i)
  have hs : (∑ i, if x i ∈ A then (1 : ℝ) else 0) ≤ 4 * (spouseVectorTotal x * Y) := by
    calc
      _ ≤ ∑ i, 4 * Y * x i := Finset.sum_le_sum fun i _ ↦ h₁ i
      _ = _ := by rw [← Finset.mul_sum, spouseVectorTotal]; ring
  exact hs.trans_lt (by linarith only [hbad])
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
theorem measure_pi_spouseProduct_lt_le {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ spouseVectorTotal y) :
    (Measure.pi (normalizedStableMaleSpouseRowLaw y))
      {x | spouseVectorTotal x * spouseVectorTotal y < (n : ℝ) / 128} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 128)) := by
  let Y := spouseVectorTotal y
  let ν := normalizedStableMaleSpouseRowLaw y
  let A : Set ℝ := Ioc (1 / (4 * Y)) (1 / (2 * Y))
  let (i : Fin n) : IsProbabilityMeasure (ν i) :=
    normalizedStableMaleSpouseRowLaw_isProbabilityMeasure y hy hs i
  have hY : 0 < Y := by linarith
  have htail := measure_pi_flagCount_lt_le ν (fun _ ↦ A) (fun _ ↦ measurableSet_Ioc)
    (normalizedStableMaleSpouseRowLaw_goodInterval_ge y hy hs)
  rw [Fintype.card_fin] at htail
  have hae : ∀ᵐ x ∂Measure.pi ν, ∀ i, 0 ≤ x i := ae_all_iff.2 fun i ↦
    ((measurePreserving_eval ν i).quasiMeasurePreserving.ae
      (ae_normalizedStableMaleSpouseRowLaw_mem_Icc y i)).mono fun _ hx ↦ hx.1
  refine (measure_mono_ae ?_).trans htail
  filter_upwards [hae] with x hx hbad
  exact flagCount_lt_of_spouseProduct_lt (A := A) hY (fun _ hi ↦ hi.1) hx hbad
theorem lintegral_lowSpouseProductVectorSection_le {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    (∫⁻ x, (lowSpouseProductVectorSet n).indicator
        (fun z ↦ spouseStabilityKernel z.1 z.2) (x, y) ∂spouseVectorLaw n) ≤
      femaleSpouseStabilityDensity y * ENNReal.ofReal (Real.exp (-(n : ℝ) / 128)) := by
  by_cases hs : 2 ≤ spouseVectorTotal y
  · let B : Set (Fin n → ℝ) :=
      {x | spouseVectorTotal x * spouseVectorTotal y < (n : ℝ) / 128}
    have htotal : Measurable (@spouseVectorTotal n) :=
      Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
    have hB : MeasurableSet B := measurableSet_lt (htotal.mul_const _) measurable_const
    have hpoint (x : Fin n → ℝ) :
        (lowSpouseProductVectorSet n).indicator (fun z ↦ spouseStabilityKernel z.1 z.2)
          (x, y) = B.indicator (fun x ↦ spouseStabilityKernel x y) x := by
      have hmem : (x, y) ∈ lowSpouseProductVectorSet n ↔ x ∈ B := by
        exact and_iff_right hs
      by_cases hx : x ∈ B
      · rw [indicator_of_mem (hmem.mpr hx), indicator_of_mem hx]
      · rw [indicator_of_notMem (hmem.not.mpr hx), indicator_of_notMem hx]
    simp_rw [hpoint]
    rw [lintegral_indicator hB, ← withDensity_apply _ hB,
      spouseStabilityKernel_withDensity_eq y hy hs, Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (measure_pi_spouseProduct_lt_le y hy hs) _
  · have hz (x : Fin n → ℝ) :
        (lowSpouseProductVectorSet n).indicator (fun z ↦ spouseStabilityKernel z.1 z.2) (x, y) =
          0 := indicator_of_notMem (fun h ↦ hs h.1) _
    simp_rw [hz, lintegral_zero]
    exact zero_le
theorem measure_stable_spouseProduct_lt_le {n : ℕ} (μ : Matching n) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
      maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128} ≤
      continuousScoreLaw n {x | IsScoreStable x μ} *
        ENNReal.ofReal (Real.exp (-(n : ℝ) / 128)) := by
  simpa only [lowSpouseProductVectorSet, mem_ofPred_eq, spouseVectorTotal,
    ← femaleSpouseTotal_eq_sum_byHusband, maleSpouseTotal] using
    measure_stable_and_spouseVectors_le_of_section μ (measurableSet_lowSpouseProductVectorSet n)
      ENNReal.ofReal_ne_top lintegral_lowSpouseProductVectorSection_le
theorem sum_measure_stable_spouseProduct_lt_le (n : ℕ) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128}) ≤
      ENNReal.ofReal (expectedNumStableMatchings n) *
        ENNReal.ofReal (Real.exp (-(n : ℝ) / 128)) := by
  calc
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ} *
        ENNReal.ofReal (Real.exp (-(n : ℝ) / 128)) :=
      Finset.sum_le_sum fun μ _ ↦ measure_stable_spouseProduct_lt_le μ
    _ = _ := by rw [← Finset.sum_mul, sum_measure_scoreStable_eq_expected]
private theorem eventually_sizeSq_mul_exp_le_neg_rpow (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (2 : ℕ) * Real.exp (-(n : ℝ) / 128) ≤
      (n : ℝ) ^ (-p) := by
  have hlog := (((isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).const_mul_left
    (128 * (p + 2))).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (1 : ℕ), hlog] with n hn hnlog
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have habs : |128 * (p + 2) * Real.log (n : ℝ)| ≤ |(n : ℝ) ^ (1 : ℝ)| := hnlog
  rw [Real.rpow_one, abs_of_nonneg hn₀.le] at habs
  have h := (le_abs_self _).trans habs
  have hl : (p + 2) * Real.log n ≤ (n : ℝ) / 128 := by linarith
  have hE : Real.exp (-(n : ℝ) / 128) ≤ (n : ℝ) ^ (-(p + 2)) := by
    rw [Real.rpow_def_of_pos hn₀]
    exact Real.exp_le_exp.mpr (by linarith only [hl])
  calc
    _ ≤ (n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ (-(p + 2)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = _ := by
      rw [← Real.rpow_two, ← Real.rpow_add hn₀, show (2 : ℝ) + -(p + 2) = -p by ring]
theorem eventually_sum_measure_stable_spouseProduct_lt_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n
        {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
          maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128}) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_expectedNumStableMatchings_le_sizeSq,
    eventually_sizeSq_mul_exp_le_neg_rpow p] with n hm hrate
  refine (sum_measure_stable_spouseProduct_lt_le n).trans ?_
  calc
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (2 : ℕ)) * ENNReal.ofReal (Real.exp (-(n : ℝ) / 128)) :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal hm) _
    _ = ENNReal.ofReal ((n : ℝ) ^ (2 : ℕ) * Real.exp (-(n : ℝ) / 128)) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hrate
private def badSpouseProductMark {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧
    maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128}
theorem eventually_sum_measure_badSpouseProductMark_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n (badSpouseProductMark μ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  have hL : ∀ᶠ n : ℕ in atTop, 2 ≤ (9 / 10 : ℝ) * Real.log n :=
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (20 / 9)).mono fun n h ↦ by
        change (20 / 9 : ℝ) ≤ Real.log (n : ℝ) at h
        linarith only [h]
  filter_upwards [eventually_sum_stable_smallSpouseTotalLog_le (p + 1),
    eventually_sum_measure_stable_spouseProduct_lt_le (p + 1), hL,
    eventually_ge_atTop (2 : ℕ)] with n hsmall hbulk hnlog hn
  let A (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
  let B (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
      maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128}
  have hcover (μ : Matching n) : badSpouseProductMark μ ⊆ A μ ∪ B μ := by
    intro x hx
    by_cases hY : 2 ≤ femaleSpouseTotal x μ
    · exact Or.inr ⟨hx.1, hY, hx.2⟩
    · exact Or.inl ⟨hx.1, (lt_of_not_ge hY).trans_le hnlog⟩
  have hn₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  let a := (n : ℝ) ^ (-(p + 1))
  have ha : 0 ≤ a := Real.rpow_nonneg hn₀.le _
  calc
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n (A μ) + continuousScoreLaw n (B μ)) :=
      Finset.sum_le_sum fun μ _ ↦ (measure_mono (hcover μ)).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal a := by
      rw [Finset.sum_add_distrib]
      exact add_le_add hsmall hbulk
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add ha ha]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = 2 * a := (two_mul _).symm
        _ ≤ (n : ℝ) * a := mul_le_mul_of_nonneg_right hn₂ ha
        _ = _ := calc
          _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(p + 1)) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hn₀, show (1 : ℝ) + -(p + 1) = -p by ring]
theorem eventually_measure_exists_stable_smallSpouseProduct_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n
      {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
        maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128} ≤
      ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_sum_measure_badSpouseProductMark_le p] with n h
  have hsub : {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
        maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128} ≤ᵐ[continuousScoreLaw n]
      ⋃ μ : Matching n, badSpouseProductMark μ := by
    filter_upwards [ae_injective_rows n] with x hx hbad
    obtain ⟨μ, hμ, hp⟩ := hbad
    exact Set.mem_iUnion.mpr ⟨μ, (isStable_profileOfScores_iff hx μ).mp hμ, hp⟩
  refine (measure_mono_ae hsub).trans ((measure_iUnion_le _).trans ?_)
  rwa [tsum_fintype]
end StepA3
end

-- PivotForwardRevealCell
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
private def forwardEligibleScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  Ioi x ×ˢ Iio y
theorem measurableSet_forwardEligibleScoreCell (x y : ℝ) :
    MeasurableSet (forwardEligibleScoreCell x y) :=
  measurableSet_Ioi.prod measurableSet_Iio
private noncomputable def stableScoreCellLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  unitScorePairLaw.restrict (nonblockingScoreCell x y)
theorem stableScoreCellLaw_restrict_forwardEligible (x y : ℝ) :
    (stableScoreCellLaw x y).restrict (forwardEligibleScoreCell x y) =
      (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio y)) := by
  rw [stableScoreCellLaw, Measure.restrict_restrict_of_subset]
  · exact (Measure.prod_restrict (Ioi x) (Iio y)).symm
  · rintro z hz hblock
    have h₁ : x < z.1 := (mem_prod.mp hz).1
    have h₂ : z.1 < x := (mem_prod.mp hblock).1
    exact (not_lt_of_ge h₁.le) h₂
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
end StepA3
end

-- PivotReverseEligibility
section
open MeasureTheory Set
open scoped ENNReal
namespace StepA3
end StepA3
end

-- PivotReverseRowLaw
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
variable {ι : Type*}
end StepA3
end

-- ReverseSuccessorIncrement
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
variable {ι : Type*}
end StepA3
end

-- ReverseCompatibilityRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- PivotReverseRelaxedColumn
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- ReverseSuccessorRotation
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
end StepA3
end

-- PivotReverseScoreSuccessor
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- PivotRelaxedArcEvents
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- FinitePrerequisites
section
namespace StepA3
end StepA3
end

-- RotationDiamond
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ σ : Equiv.Perm (Fin n)}
end StepA3
end

-- ManOptimal
section
open StableMarriage
open scoped BigOperators
namespace StepA3
variable {n : ℕ}
private def MenWeaklyPrefer (p : Profile n) (μ ν : Matching n) : Prop :=
  ∀ m, p.manRank m (μ m) ≤ p.manRank m (ν m)
private def IsManOptimal (p : Profile n) (μ : Matching n) : Prop :=
  IsStable p μ ∧ ∀ ν, IsStable p ν → MenWeaklyPrefer p μ ν
end StepA3
end

-- RotationCycle
section
namespace StepA3
open Function
end StepA3
end

-- TargetSuccessor
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ ν : Matching n}
end StepA3
end

-- RotationReachability
section
open scoped BigOperators
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n}
private inductive RotationSequence (p : Profile n) :
    Matching n → List (Equiv.Perm (Fin n)) → Matching n → Prop where
  | nil {μ : Matching n} (hμ : IsStable p μ) : RotationSequence p μ [] μ
  | cons {μ ν : Matching n} {ρ : Equiv.Perm (Fin n)} {rs : List (Equiv.Perm (Fin n))}
      (hμ : IsStable p μ) (hρ : IsExposedRotation p μ ρ)
      (rest : RotationSequence p (eliminateRotation μ ρ) rs ν) :
      RotationSequence p μ (ρ :: rs) ν
end StepA3
end

-- RotationLabels
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n}
private structure RotationLabel (n : ℕ) where
  cycle : Equiv.Perm (Fin n)
  oldPartner : Fin n → Option (Fin n)
private def rotationLabel (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : RotationLabel n :=
  ⟨ρ, fun m ↦ if ρ m = m then none else some (μ m)⟩
private def rotationLabels : Matching n → List (Equiv.Perm (Fin n)) → List (RotationLabel n)
  | _, [] => []
  | μ, ρ :: rs => rotationLabel μ ρ :: rotationLabels (eliminateRotation μ ρ) rs
end StepA3
end

-- RotationPathIndependence
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n}
end StepA3
end

-- RotationTrace
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n}
namespace RotationSequence
variable {μ ν τ : Matching n} {rs ss : List (Equiv.Perm (Fin n))}
end RotationSequence
end StepA3
end

-- RotationIdeals
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
private def Rotation (p : Profile n) (μ₀ : Matching n) :=
  {r : RotationLabel n // ∃ ν rs, RotationSequence p μ₀ rs ν ∧ r ∈ rotationLabels μ₀ rs}
end StepA3
end

-- CoexposedRotations
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
end StepA3
end

-- CoexposedRotationMultiplicity
section
open StableMarriage
open scoped BigOperators
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ : Matching n}
end StepA3
end

-- CoexposureCycleMoment
section
open StableMarriage MeasureTheory
open scoped BigOperators ENNReal
namespace StepA3
private def RealizesSuccessorPermutation {n : ℕ} (p : Profile n) (M σ : Matching n) : Prop :=
  ∀ i ∈ σ.support, IsSuccessor p M i (M (σ i))
end StepA3
end

-- PivotReverseMaskJointLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- RowCompetition
section
open Set
open scoped BigOperators
namespace StepA3
variable {ι : Type*} {J : Finset ι} {a : ι → ℝ} {A b : ℝ}
end StepA3
end

-- ReverseArcRelativeLower
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- ReverseIIDLabelGood
section
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace StepA3
section Measures
variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]
variable [Fintype α] [DiscreteMeasurableSpace α]
end Measures
end StepA3
end

-- ReverseCycleLabelMultiplicity
section
open scoped BigOperators ENNReal
namespace StepA3
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {k : ℕ} {A : Finset α} {F : α → Finset α}
end StepA3
end

-- ReverseDerangementFraction
section
open scoped ENNReal
namespace StepA3
end StepA3
end

-- PivotReverseMaskLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
private noncomputable def reverseSpouseWeights {n : ℕ} (μ : Matching n) (d : DiagonalScorePairs n) :
    Fin n → ℝ≥0∞ := fun j ↦
  ENNReal.ofReal ((diagonalPairAt d (μ.symm j)).1 / ∑ i, (diagonalPairAt d i).1)
end StepA3
end

-- PivotReverseCompetitorMass
section
open StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
private noncomputable def forwardMaskOmittedMass {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) : ℝ :=
  ∑ i : {i : Fin n // i ≠ j}, if flag ⟨(i.val, j), i.property⟩ then
    (diagonalPairAt d i.val).1 else 0
end StepA3
end

-- PivotForwardMaskProbability
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
private noncomputable def forwardCellFlag (x y : ℝ) (z : ℝ × ℝ) : Bool := by
  classical
  exact decide (z ∈ forwardEligibleScoreCell x y)
@[simp] theorem forwardCellFlag_eq_true {x y : ℝ} {z : ℝ × ℝ} :
    forwardCellFlag x y z = true ↔ z ∈ forwardEligibleScoreCell x y := by
  classical
  simp [forwardCellFlag]
theorem measurable_forwardCellFlag (x y : ℝ) : Measurable (forwardCellFlag x y) := by
  apply measurable_to_bool
  simpa only [preimage, mem_singleton_iff, forwardCellFlag_eq_true, ofPred_mem_eq]
    using measurableSet_forwardEligibleScoreCell x y
private noncomputable def forwardMaskOfScores {n : ℕ} (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (q : OffDiagonalCellIndex n) : Bool :=
  forwardCellFlag (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (z q)
theorem measurable_forwardMaskOfScores {n : ℕ} (d : DiagonalScorePairs n) :
    Measurable (forwardMaskOfScores d) :=
  measurable_pi_iff.2 fun _ ↦ (measurable_forwardCellFlag _ _).comp (measurable_pi_apply _)
private noncomputable def normalizedStableScoreCellLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  ((stableScoreCellLaw x y) univ)⁻¹ • stableScoreCellLaw x y
private instance (x y : ℝ) : IsFiniteMeasure (normalizedStableScoreCellLaw x y) := by
  constructor
  rw [normalizedStableScoreCellLaw, Measure.smul_apply, smul_eq_mul, mul_comm]
  exact (ENNReal.mul_inv_ne_top _).lt_top
private noncomputable def forwardCellFlagProbabilityLaw (x y : ℝ) : Measure Bool :=
  Measure.map (forwardCellFlag x y) (normalizedStableScoreCellLaw x y)
private noncomputable def stableOffDiagonalProbabilityLaw {n : ℕ} (d : DiagonalScorePairs n) :
    Measure (OffDiagonalScorePairs n) :=
  (offDiagonalScoreLaw n (offDiagonalNonblocking d))⁻¹ •
    (offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)
private theorem stableOffDiagonalProbabilityLaw_eq_pi {n : ℕ} (d : DiagonalScorePairs n) :
    stableOffDiagonalProbabilityLaw d = Measure.pi fun q : OffDiagonalCellIndex n ↦
      normalizedStableScoreCellLaw (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 := by
  symm
  refine Measure.pi_eq fun s _ ↦ ?_
  unfold stableOffDiagonalProbabilityLaw
  rw [offDiagonalScoreLaw_nonblocking, offDiagonalScoreLaw_restrict_nonblocking,
    Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [normalizedStableScoreCellLaw, Measure.smul_apply, smul_eq_mul,
    stableScoreCellLaw, Measure.restrict_apply_univ]
  rw [ENNReal.prod_inv_distrib (fun _ _ _ _ _ ↦ Or.inr (measure_ne_top unitScorePairLaw _)),
    Finset.prod_mul_distrib]
theorem map_forwardMaskOfScores_stableOffDiagonalProbabilityLaw {n : ℕ}
    (d : DiagonalScorePairs n) :
    Measure.map (forwardMaskOfScores d) (stableOffDiagonalProbabilityLaw d) =
      Measure.pi (fun q : OffDiagonalCellIndex n ↦
        forwardCellFlagProbabilityLaw (diagonalPairAt d q.val.1).1
          (diagonalPairAt d q.val.2).2) := by
  rw [stableOffDiagonalProbabilityLaw_eq_pi]
  let μ (q : OffDiagonalCellIndex n) :=
    normalizedStableScoreCellLaw (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2
  let f (q : OffDiagonalCellIndex n) :=
    forwardCellFlag (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2
  let : ∀ q, IsFiniteMeasure ((μ q).map (f q)) :=
    fun _ ↦ Measure.isFiniteMeasure_map _ _
  exact Measure.pi_map_pi (μ := μ) (f := f) fun _ ↦
    (measurable_forwardCellFlag _ _).aemeasurable
private theorem one_sub_mul_pos {x y : ℝ} (hx : x ∈ Ico 0 1) (hy : y ∈ Ico 0 1) :
    0 < 1 - x * y :=
  sub_pos.mpr ((mul_le_of_le_one_right hx.1 hy.2.le).trans_lt hx.2)
theorem offDiagonalScoreLaw_nonblocking_pos {n : ℕ} (d : DiagonalScorePairs n)
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) :
    0 < offDiagonalScoreLaw n (offDiagonalNonblocking d) := by
  rw [offDiagonalScoreLaw_nonblocking_of_mem_Icc d
    (fun i ↦ ⟨⟨(hd i).1.1, (hd i).1.2.le⟩, ⟨(hd i).2.1, (hd i).2.2.le⟩⟩)]
  exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun q _ ↦
    (ENNReal.ofReal_pos.mpr (one_sub_mul_pos (hd q.val.1).1 (hd q.val.2).2)).ne')
theorem offDiagonalScoreLaw_restrict_nonblocking_eq_smul_probabilityLaw {n : ℕ}
    (d : DiagonalScorePairs n)
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) :
    (offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d) =
      offDiagonalScoreLaw n (offDiagonalNonblocking d) • stableOffDiagonalProbabilityLaw d := by
  rw [stableOffDiagonalProbabilityLaw, smul_smul,
    ENNReal.mul_inv_cancel (offDiagonalScoreLaw_nonblocking_pos d hd).ne' (measure_ne_top _ _),
    one_smul]
private theorem stableScoreCellLaw_univ {x y : ℝ} (hx : x ∈ Ico 0 1) (hy : y ∈ Ico 0 1) :
    stableScoreCellLaw x y univ = ENNReal.ofReal (1 - x * y) := by
  rw [stableScoreCellLaw, Measure.restrict_apply_univ]
  exact unitScorePairLaw_nonblockingScoreCell_of_mem_Icc ⟨hx.1, hx.2.le⟩ ⟨hy.1, hy.2.le⟩
theorem forwardCellFlagProbabilityLaw_isProbabilityMeasure {x y : ℝ}
    (hx : x ∈ Ico 0 1) (hy : y ∈ Ico 0 1) :
    IsProbabilityMeasure (forwardCellFlagProbabilityLaw x y) := by
  constructor
  rw [forwardCellFlagProbabilityLaw, Measure.map_apply (measurable_forwardCellFlag x y)
    MeasurableSet.univ, preimage_univ, normalizedStableScoreCellLaw, Measure.smul_apply,
    smul_eq_mul, stableScoreCellLaw_univ hx hy]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (one_sub_mul_pos hx hy)).ne'
    ENNReal.ofReal_ne_top
theorem forwardCellFlagProbabilityLaw_true {x y : ℝ} (hx : x ∈ Ico 0 1) (hy : y ∈ Ico 0 1) :
    forwardCellFlagProbabilityLaw x y {true} = ENNReal.ofReal ((1 - x) * y / (1 - x * y)) := by
  have hX : unitScoreLaw (Ioi x) = ENNReal.ofReal (1 - x) := by
    rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ioi,
      show Ioi x ∩ Icc (0 : ℝ) 1 = Ioc x 1 by
        ext u
        exact ⟨fun ⟨h, _, h₁⟩ ↦ ⟨h, h₁⟩, fun ⟨h, h₁⟩ ↦ ⟨h, hx.1.trans h.le, h₁⟩⟩,
      Real.volume_Ioc]
  have hpre : forwardCellFlag x y ⁻¹' {true} = forwardEligibleScoreCell x y := by
    ext z
    exact forwardCellFlag_eq_true
  have hactive : stableScoreCellLaw x y (forwardEligibleScoreCell x y) =
      ENNReal.ofReal ((1 - x) * y) := by
    rw [← Measure.restrict_apply_univ, stableScoreCellLaw_restrict_forwardEligible,
      ← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ, Measure.restrict_apply_univ,
      hX, unitScoreLaw_Iio_of_mem_Icc ⟨hy.1, hy.2.le⟩,
      ENNReal.ofReal_mul (sub_nonneg.mpr hx.2.le)]
  rw [forwardCellFlagProbabilityLaw, Measure.map_apply (measurable_forwardCellFlag x y)
    (measurableSet_singleton true), hpre, normalizedStableScoreCellLaw, Measure.smul_apply,
    smul_eq_mul, stableScoreCellLaw_univ hx hy, hactive, ENNReal.ofReal_div_of_pos
    (one_sub_mul_pos hx hy), div_eq_mul_inv, mul_comm]
theorem forwardCellFlagProbabilityLaw_true_toReal_le {x y : ℝ}
    (hx : x ∈ Ico 0 1) (hy : y ∈ Ico 0 1) :
    (forwardCellFlagProbabilityLaw x y {true}).toReal ≤ y := by
  rw [forwardCellFlagProbabilityLaw_true hx hy, ENNReal.toReal_ofReal
    (div_nonneg (mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1) (one_sub_mul_pos hx hy).le),
    div_le_iff₀ (one_sub_mul_pos hx hy)]
  rw [mul_comm y (1 - x * y)]
  exact mul_le_mul_of_nonneg_right
    (sub_le_sub_left (mul_le_of_le_one_right hx.1 hy.2.le) 1) hy.1
private def forwardColumnFlag {n : ℕ} (j : Fin n) (flag : OffDiagonalCellIndex n → Bool)
    (i : {i : Fin n // i ≠ j}) : Bool :=
  flag ⟨(i.val, j), i.property⟩
theorem measurable_forwardColumnFlag {n : ℕ} (j : Fin n) : Measurable (forwardColumnFlag j) :=
  measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _
theorem map_forwardColumnFlag_stableOffDiagonalProbabilityLaw {n : ℕ}
    (d : DiagonalScorePairs n) (j : Fin n)
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) :
    Measure.map (fun z ↦ forwardColumnFlag j (forwardMaskOfScores d z))
        (stableOffDiagonalProbabilityLaw d) =
      Measure.pi (fun i : {i : Fin n // i ≠ j} ↦
        forwardCellFlagProbabilityLaw (diagonalPairAt d i.val).1 (diagonalPairAt d j).2) := by
  classical
  let inColumn (q : OffDiagonalCellIndex n) : Prop := q.val.2 = j
  let J := {i : Fin n // i ≠ j}
  let ν (q : OffDiagonalCellIndex n) :=
    forwardCellFlagProbabilityLaw (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2
  let νj (i : J) :=
    forwardCellFlagProbabilityLaw (diagonalPairAt d i.val).1 (diagonalPairAt d j).2
  let : ∀ q, IsProbabilityMeasure (ν q) :=
    fun q ↦ forwardCellFlagProbabilityLaw_isProbabilityMeasure (hd q.val.1).1 (hd q.val.2).2
  let : ∀ i, IsProbabilityMeasure (νj i) :=
    fun i ↦ forwardCellFlagProbabilityLaw_isProbabilityMeasure (hd i.val).1 (hd j).2
  let e : Subtype inColumn ≃ J :=
    { toFun := fun q ↦ ⟨q.val.val.1, q.property ▸ q.val.property⟩
      invFun := fun i ↦ ⟨⟨(i.val, j), i.property⟩, rfl⟩
      left_inv := fun q ↦ Subtype.ext (Subtype.ext (Prod.ext rfl q.property.symm))
      right_inv := fun _ ↦ rfl }
  have hproj : MeasurePreserving (fun f (q : Subtype inColumn) ↦ f q.val)
      (Measure.pi ν) (Measure.pi fun q : Subtype inColumn ↦ ν q.val) :=
    measurePreserving_fst.comp (measurePreserving_piEquivPiSubtypeProd ν inColumn)
  have hν : (fun q : Subtype inColumn ↦ ν q.val) = fun q ↦ νj (e q) := by
    funext q
    change forwardCellFlagProbabilityLaw (diagonalPairAt d q.val.val.1).1
      (diagonalPairAt d q.val.val.2).2 =
      forwardCellFlagProbabilityLaw (diagonalPairAt d q.val.val.1).1 (diagonalPairAt d j).2
    rw [show q.val.val.2 = j from q.property]
  rw [hν] at hproj
  have hcol : MeasurePreserving (forwardColumnFlag j) (Measure.pi ν) (Measure.pi νj) :=
    (measurePreserving_piCongrLeft νj e).comp hproj
  exact (hcol.comp ⟨measurable_forwardMaskOfScores d,
    map_forwardMaskOfScores_stableOffDiagonalProbabilityLaw d⟩).map_eq
end StepA3
end

-- WeightedBoolProductTail
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA3
private theorem exp_le_secant_on_unit {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.exp x ≤ 1 + (Real.exp 1 - 1) * x := by
  have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (sub_nonneg.mpr hx.2) hx.1 (sub_add_cancel (1 : ℝ) x)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  linarith
private theorem lintegral_exp_weightedBool_le (ν : Measure Bool) [IsProbabilityMeasure ν]
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (∫⁻ b, ENNReal.ofReal (Real.exp (if b then u else 0)) ∂ν) ≤
      ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * u * (ν {true}).toReal)) := by
  have hmass : (ν {true}).toReal + (ν {false}).toReal = 1 := by
    have he := lintegral_fintype (μ := ν) (fun _ : Bool ↦ (1 : ℝ≥0∞))
    simp only [lintegral_const, measure_univ, mul_one, Fintype.sum_bool, one_mul] at he
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← he, ENNReal.toReal_one]
  have hp : 0 ≤ (ν {true}).toReal := ENNReal.toReal_nonneg
  rw [lintegral_fintype, Fintype.sum_bool]
  simp only [Bool.coe_false, ite_true, ite_false, Real.exp_zero]
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν {true}),
    ← ENNReal.ofReal_toReal (measure_ne_top ν {false}),
    ← ENNReal.ofReal_mul (Real.exp_pos u).le, ← ENNReal.ofReal_mul zero_le_one,
    ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos u).le hp)
      (mul_nonneg zero_le_one ENNReal.toReal_nonneg)]
  simp only [ENNReal.toReal_ofReal hp]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (1 + (Real.exp 1 - 1) * u) * (ν {true}).toReal + 1 * (ν {false}).toReal :=
      add_le_add (mul_le_mul_of_nonneg_right (exp_le_secant_on_unit hu) hp) le_rfl
    _ = ((Real.exp 1 - 1) * u * (ν {true}).toReal) + 1 := by linarith only [hmass]
    _ ≤ _ := Real.add_one_le_exp _
theorem measure_pi_weightedBoolTail_le {ι : Type*} [Fintype ι]
    (ν : ι → Measure Bool) [∀ i, IsProbabilityMeasure (ν i)]
    (w : ι → ℝ) {B : ℝ} (t : ℝ) (hB : 0 < B) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ B) :
    (Measure.pi ν) {f | t < ∑ i, if f i then w i else 0} ≤
      ENNReal.ofReal (Real.exp ((-t + (Real.exp 1 - 1) *
        ∑ i, w i * (ν i {true}).toReal) / B)) := by
  let X (i : ι) (b : Bool) := ENNReal.ofReal (Real.exp (if b then w i / B else 0))
  let C (i : ι) := ((Real.exp 1 - 1) * (w i * (ν i {true}).toReal)) / B
  let F (f : ι → Bool) := ENNReal.ofReal (Real.exp ((-t + ∑ i, if f i then w i else 0) / B))
  have hX (i : ι) : Measurable (X i) := measurable_of_finite _
  have hXpi (i : ι) : Measurable (fun f : ι → Bool ↦ X i (f i)) :=
    (hX i).comp (measurable_pi_apply i)
  have hfactor (f : ι → Bool) :
      F f = ENNReal.ofReal (Real.exp (-t / B)) * ∏ i, X i (f i) := by
    unfold F X
    rw [add_div, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, Finset.sum_div,
      Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    cases f i <;> simp
  have hmgf (i : ι) :
      (∫⁻ f : ι → Bool, X i (f i) ∂Measure.pi ν) ≤ ENNReal.ofReal (Real.exp (C i)) := by
    rw [(measurePreserving_eval ν i).lintegral_comp (hX i)]
    have hunit : w i / B ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (hw i).1 hB.le, (div_le_one hB).mpr (hw i).2⟩
    have hC : C i = (Real.exp 1 - 1) * (w i / B) * (ν i {true}).toReal := by
      unfold C
      ring
    rw [hC]
    exact lintegral_exp_weightedBool_le (ν i) hunit
  calc
    _ ≤ ∫⁻ f, F f ∂Measure.pi ν := by
      apply meas_le_lintegral₀ (measurable_of_finite F).aemeasurable
      intro f hf
      have harg : 0 ≤ (-t + ∑ i, if f i then w i else 0) / B :=
        div_nonneg (by simpa only [neg_add_eq_sub] using sub_nonneg.mpr hf.le) hB.le
      simpa only [F, Real.exp_zero, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr harg)
    _ = ENNReal.ofReal (Real.exp (-t / B)) *
        ∏ i, ∫⁻ f : ι → Bool, X i (f i) ∂Measure.pi ν := by
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
theorem measure_pi_weightedBoolTail_le_of_mean_le {ι : Type*} [Fintype ι]
    (ν : ι → Measure Bool) [∀ i, IsProbabilityMeasure (ν i)]
    (w : ι → ℝ) {B : ℝ} (t : ℝ) (hB : 0 < B) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ B)
    {m : ℝ} (hm : (∑ i, w i * (ν i {true}).toReal) ≤ m) :
    (Measure.pi ν) {f | t < ∑ i, if f i then w i else 0} ≤
      ENNReal.ofReal (Real.exp ((-t + (Real.exp 1 - 1) * m) / B)) := by
  have he : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr (by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (zero_le_one : (0 : ℝ) ≤ 1))
  refine (measure_pi_weightedBoolTail_le ν w t hB hw).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  exact div_le_div_of_nonneg_right
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm he)) hB.le
end StepA3
end

-- PivotEligibleMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
theorem measure_forwardMaskOmittedMass_gt_le {n : ℕ} (d : DiagonalScorePairs n)
    (j : Fin n) {B u : ℝ}
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1)
    (hX : 0 < ∑ i, (diagonalPairAt d i).1) (hB : 0 < B)
    (hw : ∀ i, (diagonalPairAt d i).1 / (∑ l, (diagonalPairAt d l).1) ≤ B)
    (hy : 2 * (Real.exp 1 - 1) * (diagonalPairAt d j).2 ≤ u) :
    (stableOffDiagonalProbabilityLaw d)
      {z | u * (∑ i, (diagonalPairAt d i).1) <
        forwardMaskOmittedMass d (forwardMaskOfScores d z) j} ≤
      ENNReal.ofReal (Real.exp (-u / (2 * B))) := by
  let X := ∑ i, (diagonalPairAt d i).1
  let y := (diagonalPairAt d j).2
  let J := {i : Fin n // i ≠ j}
  let ν (i : J) := forwardCellFlagProbabilityLaw (diagonalPairAt d i.val).1 y
  let w (i : J) := (diagonalPairAt d i.val).1 / X
  let g (z : OffDiagonalScorePairs n) := forwardColumnFlag j (forwardMaskOfScores d z)
  let E : Set (J → Bool) := {b | u < ∑ i, if b i then w i else 0}
  let : ∀ i : J, IsProbabilityMeasure (ν i) :=
    fun i ↦ forwardCellFlagProbabilityLaw_isProbabilityMeasure (hd i.val).1 (hd j).2
  have hw₀ (i : J) : 0 ≤ w i := div_nonneg (hd i.val).1.1 hX.le
  have hsum : (∑ i : J, w i) ≤ 1 := by
    let v (i : Fin n) := (diagonalPairAt d i).1 / X
    change (∑ i : {i : Fin n // i ≠ j}, v i.val) ≤ _
    rw [← Finset.sum_subtype (Finset.univ.filter (· ≠ j)) (by simp) v]
    calc
      _ ≤ ∑ i, v i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ ↦ div_nonneg (hd i).1.1 hX.le)
      _ = 1 := by simp only [v, ← Finset.sum_div, X, div_self hX.ne']
  have hmean : (∑ i : J, w i * (ν i {true}).toReal) ≤ y := calc
    _ ≤ ∑ i : J, w i * y := Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (forwardCellFlagProbabilityLaw_true_toReal_le
        (hd i.val).1 (hd j).2) (hw₀ i)
    _ = (∑ i : J, w i) * y := (Finset.sum_mul ..).symm
    _ ≤ 1 * y := mul_le_mul_of_nonneg_right hsum (hd j).2.1
    _ = y := one_mul _
  have htail := measure_pi_weightedBoolTail_le_of_mean_le ν w u hB
    (fun i ↦ ⟨hw₀ i, hw i.val⟩) hmean
  change (Measure.pi ν) E ≤ _ at htail
  have hg : Measurable g := (measurable_forwardColumnFlag j).comp
    (measurable_forwardMaskOfScores d)
  rw [← map_forwardColumnFlag_stableOffDiagonalProbabilityLaw d j hd,
    Measure.map_apply hg MeasurableSet.of_discrete] at htail
  have hE : g ⁻¹' E = {z | u * X < forwardMaskOmittedMass d (forwardMaskOfScores d z) j} := by
    ext z
    change (u < ∑ i : J, if g z i then w i else 0) ↔ _
    have he : (∑ i : J, if g z i then w i else 0) =
        forwardMaskOmittedMass d (forwardMaskOfScores d z) j / X := by
      rw [forwardMaskOmittedMass, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change (if g z i then w i else 0) =
        (if g z i then (diagonalPairAt d i.val).1 else 0) / X
      split <;> simp [w, *]
    rw [he, lt_div_iff₀ hX]
    rfl
  rw [hE] at htail
  refine htail.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  rw [show -u / (2 * B) = (-u / 2) / B by ring]
  exact div_le_div_of_nonneg_right (by linarith only [hy]) hB.le
private def badForwardMask {n : ℕ} (d : DiagonalScorePairs n) (u : ℝ) : Set (OffDiagonalScorePairs n) :=
  ⋃ j : Fin n, {z | u * (∑ i, (diagonalPairAt d i).1) <
    forwardMaskOmittedMass d (forwardMaskOfScores d z) j}
theorem measurableSet_badForwardMask {n : ℕ} (d : DiagonalScorePairs n) (u : ℝ) :
    MeasurableSet (badForwardMask d u) := by
  apply MeasurableSet.iUnion
  intro j
  exact (measurable_forwardMaskOfScores d)
    (MeasurableSet.of_discrete : MeasurableSet {f : OffDiagonalCellIndex n → Bool |
      u * (∑ i, (diagonalPairAt d i).1) < forwardMaskOmittedMass d f j})
theorem measure_badForwardMask_le {n : ℕ} (d : DiagonalScorePairs n) {B u : ℝ}
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1)
    (hX : 0 < ∑ i, (diagonalPairAt d i).1) (hB : 0 < B)
    (hw : ∀ i, (diagonalPairAt d i).1 / (∑ l, (diagonalPairAt d l).1) ≤ B)
    (hy : ∀ j, 2 * (Real.exp 1 - 1) * (diagonalPairAt d j).2 ≤ u) :
    (stableOffDiagonalProbabilityLaw d) (badForwardMask d u) ≤
      ENNReal.ofReal ((n : ℝ) * Real.exp (-u / (2 * B))) := by
  refine (measure_iUnion_le _).trans ?_
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _j : Fin n, ENNReal.ofReal (Real.exp (-u / (2 * B))) :=
      Finset.sum_le_sum fun j _ ↦ measure_forwardMaskOmittedMass_gt_le d j hd hX hB hw (hy j)
    _ = _ := by simp [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg n)]
theorem eventually_forwardMaskRate (Cx Cy p : ℝ) (hx : 0 < Cx) :
    ∀ᶠ n : ℕ in atTop, 1 < n ∧
      2 * (Real.exp 1 - 1) * (Cy * (n : ℝ) ^ (-3 / 5 : ℝ) * Real.log n) ≤
        (n : ℝ) ^ (-11 / 20 : ℝ) ∧
      (n : ℝ) * Real.exp (-((n : ℝ) ^ (-11 / 20 : ℝ)) /
        (2 * (Cx * Real.log n / n))) ≤ (n : ℝ) ^ (-p) := by
  have h₁ := (((isLittleO_log_rpow_atTop (r := (1 / 20 : ℝ)) (by norm_num)).const_mul_left
    (2 * (Real.exp 1 - 1) * Cy)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  have h₂ := (((isLittleO_log_rpow_rpow_atTop (s := (9 / 20 : ℝ)) 2 (by norm_num)).const_mul_left
    (2 * Cx * (p + 1))).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (1 : ℕ), h₁, h₂] with n hn h₁n h₂n
  have hn₁ : 1 < (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn₁
  have hb : 0 < 2 * (Cx * Real.log (n : ℝ) / n) := by positivity
  have hm : 2 * (Real.exp 1 - 1) * Cy * Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := by
    have h : |2 * (Real.exp 1 - 1) * Cy * Real.log (n : ℝ)| ≤
        |(n : ℝ) ^ (1 / 20 : ℝ)| := h₁n
    rw [abs_of_nonneg (Real.rpow_nonneg hn₀.le _)] at h
    exact (le_abs_self _).trans h
  have hh : 2 * Cx * (p + 1) * Real.log (n : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) ^ (9 / 20 : ℝ) := by
    have h : |2 * Cx * (p + 1) * Real.log (n : ℝ) ^ (2 : ℝ)| ≤
        |(n : ℝ) ^ (9 / 20 : ℝ)| := h₂n
    rw [Real.rpow_two, abs_of_nonneg (Real.rpow_nonneg hn₀.le _)] at h
    exact (le_abs_self _).trans h
  have hm' := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hn₀.le (-3 / 5 : ℝ))
  rw [← Real.rpow_add hn₀, show (1 / 20 : ℝ) + (-3 / 5) = -11 / 20 by norm_num] at hm'
  have hE : (p + 1) * Real.log (n : ℝ) ≤
      (n : ℝ) ^ (-11 / 20 : ℝ) / (2 * (Cx * Real.log (n : ℝ) / n)) := by
    apply (le_div_iff₀ hb).mpr
    rw [show (p + 1) * Real.log (n : ℝ) * (2 * (Cx * Real.log (n : ℝ) / n)) =
      (2 * Cx * (p + 1) * Real.log (n : ℝ) ^ (2 : ℕ)) / n by ring]
    apply (div_le_iff₀ hn₀).mpr
    have hpow : (n : ℝ) ^ (-11 / 20 : ℝ) * n = (n : ℝ) ^ (9 / 20 : ℝ) := calc
      _ = (n : ℝ) ^ (-11 / 20 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn₀]; norm_num
    rwa [hpow]
  refine ⟨hn, ?_, ?_⟩
  · linarith [hm']
  · calc
      _ ≤ (n : ℝ) * Real.exp (-((p + 1) * Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          rw [neg_div]
          exact neg_le_neg hE)) hn₀.le
      _ = (n : ℝ) ^ (-p) := by
        rw [show -((p + 1) * Real.log (n : ℝ)) = Real.log (n : ℝ) * (-(p + 1)) by ring,
          ← Real.rpow_def_of_pos hn₀]
        calc
          _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(p + 1)) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hn₀, show (1 : ℝ) + (-(p + 1)) = -p by ring]
theorem eventually_measure_badForwardMask_le (Cx Cy p : ℝ) (hx : 0 < Cx) :
    ∀ᶠ n : ℕ in atTop, ∀ d : DiagonalScorePairs n,
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) →
      0 < (∑ i, (diagonalPairAt d i).1) →
      (∀ i, (diagonalPairAt d i).1 / (∑ j, (diagonalPairAt d j).1) ≤ Cx * Real.log n / n) →
      (∀ j, (diagonalPairAt d j).2 ≤ Cy * (n : ℝ) ^ (-3 / 5 : ℝ) * Real.log n) →
      (stableOffDiagonalProbabilityLaw d) (badForwardMask d ((n : ℝ) ^ (-11 / 20 : ℝ))) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_forwardMaskRate Cx Cy p hx] with n h d hd hX hw hy
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast h.1)
  have he : 0 ≤ 2 * (Real.exp 1 - 1) := by
    have := Real.one_le_exp (by norm_num : 0 ≤ (1 : ℝ))
    linarith
  exact (measure_badForwardMask_le d hd hX (by positivity) hw (fun j ↦
    (mul_le_mul_of_nonneg_left (hy j) he).trans h.2.1)).trans
    (ENNReal.ofReal_le_ofReal h.2.2)
theorem eventually_restrict_nonblocking_badForwardMask_le (Cx Cy p : ℝ) (hx : 0 < Cx) :
    ∀ᶠ n : ℕ in atTop, ∀ d : DiagonalScorePairs n,
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) →
      0 < (∑ i, (diagonalPairAt d i).1) →
      (∀ i, (diagonalPairAt d i).1 / (∑ j, (diagonalPairAt d j).1) ≤ Cx * Real.log n / n) →
      (∀ j, (diagonalPairAt d j).2 ≤ Cy * (n : ℝ) ^ (-3 / 5 : ℝ) * Real.log n) →
      ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d))
        (badForwardMask d ((n : ℝ) ^ (-11 / 20 : ℝ))) ≤
      offDiagonalScoreLaw n (offDiagonalNonblocking d) * ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_measure_badForwardMask_le Cx Cy p hx] with n h d hd hX hw hy
  rw [offDiagonalScoreLaw_restrict_nonblocking_eq_smul_probabilityLaw d hd,
    Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right (h d hd hX hw hy) _
theorem femaleScore_le_of_share_of_band {n : ℕ} {Y y C : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C) (hY : 0 < Y) (hY' : Y ≤ (n : ℝ) ^ (2 / 5 : ℝ))
    (hy : y / Y ≤ C * Real.log n / n) :
    y ≤ C * (n : ℝ) ^ (-3 / 5 : ℝ) * Real.log n := by
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog := Real.log_nonneg hn₁
  have he : (n : ℝ) ^ (2 / 5 : ℝ) / n = (n : ℝ) ^ (-3 / 5 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hn₀]
    norm_num
  calc
    _ ≤ (C * Real.log n / n) * Y := (div_le_iff₀ hY).mp hy
    _ ≤ (C * Real.log n / n) * (n : ℝ) ^ (2 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hY' (by positivity)
    _ = C * ((n : ℝ) ^ (2 / 5 : ℝ) / n) * Real.log n := by ring
    _ = _ := by rw [he]
theorem measurableSet_jointBadForwardMask (n : ℕ) (u : ℝ) :
    MeasurableSet {z : DiagonalScorePairs n × OffDiagonalScorePairs n |
      z.2 ∈ badForwardMask z.1 u} := by
  let Ω := DiagonalScorePairs n × OffDiagonalScorePairs n
  let x (i : Fin n) (z : Ω) := (diagonalPairAt z.1 i).1
  let y (j : Fin n) (z : Ω) := (diagonalPairAt z.1 j).2
  let idx (i : Fin n) : {q : ScorePairIndex n // q.1 = q.2} := ⟨(i, i), rfl⟩
  have hx (i : Fin n) : Measurable (x i) :=
    ((measurable_pi_apply (idx i)).comp measurable_fst).fst
  have hy (j : Fin n) : Measurable (y j) :=
    ((measurable_pi_apply (idx j)).comp measurable_fst).snd
  have homit (j : Fin n) :
      Measurable (fun z : Ω ↦ forwardMaskOmittedMass z.1 (forwardMaskOfScores z.1 z.2) j) := by
    apply Finset.measurable_sum
    intro i _
    let q : OffDiagonalCellIndex n := ⟨(i.val, j), i.property⟩
    let zq (z : Ω) := z.2 q
    have hzq : Measurable zq := (measurable_pi_apply q).comp measurable_snd
    have hactive : MeasurableSet {z : Ω | forwardMaskOfScores z.1 z.2 q = true} := by
      have he : {z : Ω | forwardMaskOfScores z.1 z.2 q = true} =
          {z | x i.val z < (zq z).1} ∩ {z | (zq z).2 < y j z} := by
        ext z
        exact forwardCellFlag_eq_true.trans Set.mem_prod
      rw [he]
      exact (measurableSet_lt (hx i.val) hzq.fst).inter (measurableSet_lt hzq.snd (hy j))
    exact Measurable.ite hactive (hx i.val) measurable_const
  have he : {z : Ω | z.2 ∈ badForwardMask z.1 u} =
      ⋃ j : Fin n, {z : Ω | u * (∑ i, x i z) <
        forwardMaskOmittedMass z.1 (forwardMaskOfScores z.1 z.2) j} := by
    ext z
    simp only [badForwardMask, mem_ofPred_eq, mem_iUnion, x]
  rw [he]
  exact MeasurableSet.iUnion fun j ↦ measurableSet_lt
    (measurable_const.mul (Finset.measurable_sum _ (fun i _ ↦ hx i))) (homit j)
private def badForwardMaskAnchorEvent {n : ℕ} (μ : Matching n) (C : Set (DiagonalScorePairs n))
    (u : ℝ) : Set (ScoreProfile n) :=
  {x | let z := splitScorePairs μ x
       IsScoreStable x μ ∧ z.1 ∈ C ∧ z.2 ∈ badForwardMask z.1 u}
theorem measure_badForwardMaskAnchorEvent_le {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) (u : ℝ) {a : ℝ≥0∞} (ha : a ≠ ⊤)
    (h : ∀ d ∈ C,
      ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)) (badForwardMask d u) ≤
        offDiagonalScoreLaw n (offDiagonalNonblocking d) * a) :
    continuousScoreLaw n (badForwardMaskAnchorEvent μ C u) ≤
      continuousScoreLaw n {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C} * a := by
  let S : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}
  let B : Set (ScoreProfile n) := (splitScorePairs μ) ⁻¹'
    {z | z.2 ∈ badForwardMask z.1 u}
  have hB : MeasurableSet B := (measurableSet_jointBadForwardMask n u).preimage
    (splitScorePairs μ).measurable
  let ν (d : DiagonalScorePairs n) := (offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)
  have hS : continuousScoreLaw n S = ∫⁻ d in C, (ν d) univ ∂diagonalScoreLaw n := by
    simpa only [lintegral_const, one_mul, ν, S, Measure.restrict_apply_univ] using
      (continuousScoreLaw_lintegral_stable_and_diagonal μ hC
        (f := fun _ ↦ (1 : ℝ≥0∞)) measurable_const)
  have hsection (d : DiagonalScorePairs n) :
      (∫⁻ z, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) ((splitScorePairs μ).symm (d, z)) ∂ν d) =
        (ν d) (badForwardMask d u) := by
    rw [← lintegral_indicator_one (measurableSet_badForwardMask d u)]
    apply lintegral_congr
    intro z
    have he : ((splitScorePairs μ).symm (d, z)) ∈ B ↔ z ∈ badForwardMask d u := by
      change ((splitScorePairs μ) ((splitScorePairs μ).symm (d, z))).2 ∈
        badForwardMask ((splitScorePairs μ) ((splitScorePairs μ).symm (d, z))).1 u ↔ _
      rw [MeasurableEquiv.apply_symm_apply]
    by_cases hz : z ∈ badForwardMask d u
    · rw [Set.indicator_of_mem (he.mpr hz), Set.indicator_of_mem hz]
      rfl
    · rw [Set.indicator_of_notMem (he.not.mpr hz), Set.indicator_of_notMem hz]
  have hBS : badForwardMaskAnchorEvent μ C u = B ∩ S := by
    ext x
    change (_ ∧ _ ∧ _) ↔ _ ∧ (_ ∧ _)
    tauto
  calc
    _ = ∫⁻ d in C, ∫⁻ z, B.indicator (fun _ ↦ (1 : ℝ≥0∞))
        ((splitScorePairs μ).symm (d, z)) ∂ν d ∂diagonalScoreLaw n := by
      rw [hBS, ← Measure.restrict_apply hB, ← lintegral_indicator_one hB]
      exact continuousScoreLaw_lintegral_stable_and_diagonal μ hC
        (measurable_const.indicator hB)
    _ ≤ ∫⁻ d in C, (ν d) univ * a ∂diagonalScoreLaw n := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem (μ := diagonalScoreLaw n) hC] with d hd
      rw [hsection d]
      simpa only [ν, Measure.restrict_apply_univ] using h d hd
    _ = _ := by rw [lintegral_mul_const' a _ ha, ← hS]
theorem eventually_sum_measure_badForwardMaskAnchorEvent_le (Cx Cy p : ℝ) (hx : 0 < Cx) :
    ∀ᶠ n : ℕ in atTop, ∀ C : Set (DiagonalScorePairs n), MeasurableSet C →
      (∀ d ∈ C,
        (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) ∧
        0 < (∑ i, (diagonalPairAt d i).1) ∧
        (∀ i, (diagonalPairAt d i).1 / (∑ j, (diagonalPairAt d j).1) ≤ Cx * Real.log n / n) ∧
        (∀ j, (diagonalPairAt d j).2 ≤ Cy * (n : ℝ) ^ (-3 / 5 : ℝ) * Real.log n)) →
      (∑ μ : Matching n, continuousScoreLaw n
        (badForwardMaskAnchorEvent μ C ((n : ℝ) ^ (-11 / 20 : ℝ)))) ≤
        ENNReal.ofReal (expectedNumStableMatchings n) * ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_restrict_nonblocking_badForwardMask_le Cx Cy p hx]
    with n h C hC hband
  let a := ENNReal.ofReal ((n : ℝ) ^ (-p))
  calc
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ} * a := by
      refine Finset.sum_le_sum fun μ _ ↦ ?_
      refine (measure_badForwardMaskAnchorEvent_le μ hC _ ENNReal.ofReal_ne_top
        (fun d hd ↦ ?_)).trans (mul_le_mul_left (measure_mono fun _ hx ↦ hx.1) a)
      obtain ⟨hd₁, hX, hw, hy⟩ := hband d hd
      exact h d hd₁ hX hw hy
    _ = _ := by rw [← Finset.sum_mul, sum_measure_scoreStable_eq_expected]
end StepA3
end

-- PivotForwardRevealRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
private abbrev ForwardRevealedMaleScores {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  ForwardActiveCellIndex flag → ℝ
private abbrev ForwardInactiveColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  (i : Fin n) → ForwardInactiveColumnIndex flag i → ℝ × ℝ
private def forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    OffDiagonalScorePairs n → ForwardRevealedMaleScores flag × ForwardInactiveColumns flag :=
  Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag
end StepA3
end

-- PivotForwardPivotReadout
section
open MeasureTheory Set StableMarriage
namespace StepA3
end StepA3
end

-- SingletonIdealAnchor
section
namespace StepA3
variable {α : Type*} [PartialOrder α]
end StepA3
end

-- SingletonRotationAnchor
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
end StepA3
end

-- ReverseRotationIdeals
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n} {σ : Equiv.Perm (Fin n)}
end StepA3
end

-- PivotCrossBlocker
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n} {A N : Matching n} {ρ : Equiv.Perm (Fin n)}
end StepA3
end

-- PivotReversePermutationCompatibility
section
open StableMarriage
namespace StepA3
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
end StepA3
end

-- ReverseSupportWeightUpper
section
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- PivotCompatibilityLoss
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- UndoMaximalSubset
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n}
end StepA3
end

-- RotationUndoSequences
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {hopt : IsManOptimal p μ₀}
end StepA3
end

-- PivotIncidenceCounting
section
open StableMarriage
open scoped BigOperators
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ₀ ν μ : Matching n} {hopt : IsManOptimal p μ₀}
namespace PivotDecoration
variable {K : ℕ} {r : Rotation p μ₀}
end PivotDecoration
end StepA3
end

-- PivotCompatibleLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- ReverseIncrementColumnTail
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
variable {ι : Type*}
end StepA3
end

-- PivotReverseIncrementFilter
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- PivotReverseFilteredCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- ReverseColoredPermutations
section
open scoped BigOperators
namespace StepA3
end StepA3
end

-- CoexposureGaussianSum
section
open scoped BigOperators ENNReal
open Finset Filter
namespace StepA3
end StepA3
end

-- ReverseQuadraticGaussian
section
open Finset
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- ReverseCycleCollectionMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- PivotReverseMaskMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- MeasureCountFilterLoss
section
open MeasureTheory
open scoped ENNReal
namespace StepA3
variable {Ω : Type*} [MeasurableSpace Ω]
end StepA3
end

-- ReverseCycleTypeWeightTransfer
section
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- ShortCycleChebyshev
section
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- UniformShortCycleMoments
section
open Equiv Equiv.Perm
open scoped BigOperators
namespace StepA3
variable {α : Type*} [Fintype α] [DecidableEq α]
end StepA3
end

-- PivotReverseFilterMoment
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- PivotScoreLock
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}
end StepA3
end

-- PivotForwardExposureReveal
section
open MeasureTheory Set StableMarriage
namespace StepA3
end StepA3
end

-- PivotEligibilityScale
section
open Filter Real
open scoped BigOperators ENNReal Topology
namespace StepA3
end StepA3
end

-- PivotEligibleRevealControls
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
private def reverseDiagonalMaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).1
namespace ReverseMaskGeometry
variable {n : ℕ} {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
  {μ ρ : Matching n} {s u p : ℝ}
end ReverseMaskGeometry
end StepA3
end

-- PivotSpouseBandMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
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
theorem eventually_sum_measure_badForwardMaskAnchorEvent_on_pivotBaseDiagonalBand_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, (∑ μ : Matching n, continuousScoreLaw n
      (badForwardMaskAnchorEvent μ (pivotBaseDiagonalBand n) ((n : ℝ) ^ (-11 / 20 : ℝ)))) ≤
      ENNReal.ofReal (expectedNumStableMatchings n) * ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_sum_measure_badForwardMaskAnchorEvent_le 2048 12 p (by norm_num),
    eventually_gt_atTop (0 : ℕ)] with n h hn
  apply h _ (measurableSet_pivotBaseDiagonalBand n)
  intro d hd
  obtain ⟨hscore, hY, hY', hXY, hy, hx⟩ := hd
  have hY₀ : 0 < pivotDiagonalFemaleTotal d := by linarith
  have hX₀ : 0 < reverseDiagonalMaleTotal d :=
    pos_of_mul_pos_left ((div_pos (Nat.cast_pos.mpr hn) (by norm_num)).trans_le hXY) hY₀.le
  refine ⟨hscore, hX₀, ?_, ?_⟩
  · exact fun i ↦ normalizedMaleScore_le_of_spouseProduct hn hY hXY (hx i)
  · exact fun i ↦ femaleScore_le_of_share_of_band hn (by norm_num) hY₀ hY' (hy i)
end StepA3
end

-- CoexposureScoreMomentBound
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
end StepA3
end

-- CoexposureScoreRefutation
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
private def smallScoreException {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ smallSpouseScoreSet n}
private def largeRelativeScoreException {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ largeRelativeSpouseScoreSet n}
private theorem badStableScoreMass_le_cutoffSums {n : ℕ} (μ : Matching n) :
    continuousScoreLaw n (badStableSpouseScores n μ) ≤
      continuousScoreLaw n (smallScoreException μ) +
        continuousScoreLaw n (largeRelativeScoreException μ) +
          continuousScoreLaw n (badMaleSpouseScores μ) := by
  classical
  let exceptions : Set (ScoreProfile n) :=
    (smallScoreException μ ∪ largeRelativeScoreException μ) ∪ badMaleSpouseScores μ
  have hsub : badStableSpouseScores n μ ≤ᶠ[ae (continuousScoreLaw n)] exceptions := by
    filter_upwards [ae_unitOpen_scores n] with x hx
    intro hbad
    let y := femaleSpouseByHusband μ x
    have hy (j : Fin n) : y j ∈ Ioo (0 : ℝ) 1 :=
      hx (.inr (μ j)) (μ.symm (μ j))
    have hs_eq : femaleSpouseTotal x μ = spouseVectorTotal y :=
      femaleSpouseTotal_eq_sum_byHusband μ x
    by_cases hs : 2 ≤ femaleSpouseTotal x μ
    · by_cases hw : ∀ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤
          12 * Real.log n / n
      · have hm : ¬∀ i, maleSpouseScore x μ i ≤
            8 * Real.log n / (femaleSpouseTotal x μ - 1) :=
          fun hm ↦ hbad.2 ⟨hs, hw, hm⟩
        obtain ⟨i, hi⟩ := not_forall.mp hm
        exact Or.inr ⟨hbad.1, hs, i, lt_of_not_ge hi⟩
      · obtain ⟨j, hj⟩ := not_forall.mp hw
        have htotal : spouseVectorTotal y ≤ (n : ℝ) :=
          calc
            spouseVectorTotal y ≤ ∑ _ : Fin n, (1 : ℝ) :=
              Finset.sum_le_sum fun i _ ↦ (hy i).2.le
            _ = _ := by simp
        refine Or.inl (Or.inr ⟨hbad.1, fun i ↦ (hy i).1.le, hs_eq ▸ hs,
          htotal, μ.symm j, ?_⟩)
        change 12 * Real.log n / n < y (μ.symm j) / spouseVectorTotal y
        rw [← hs_eq]
        simpa only [y, femaleSpouseByHusband, Equiv.apply_symm_apply] using lt_of_not_ge hj
    · exact Or.inl (Or.inl ⟨hbad.1, fun i ↦ (hy i).1.le, hs_eq ▸ lt_of_not_ge hs⟩)
  calc
    _ ≤ continuousScoreLaw n exceptions := measure_mono_ae hsub
    _ ≤ continuousScoreLaw n (smallScoreException μ ∪ largeRelativeScoreException μ) +
        continuousScoreLaw n (badMaleSpouseScores μ) := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_union_le _ _) le_rfl
private theorem badScoreMass_le_cutoffSums (n : ℕ) :
    continuousScoreLaw n (goodCoexposureScores n)ᶜ ≤
      (∑ μ : Matching n, continuousScoreLaw n (smallScoreException μ)) +
      (∑ μ : Matching n, continuousScoreLaw n (largeRelativeScoreException μ)) +
      ∑ μ : Matching n, continuousScoreLaw n (badMaleSpouseScores μ) := by
  calc
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n (badStableSpouseScores n μ) :=
      measure_badCoexposureScores_le_sum n
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n (smallScoreException μ) +
        continuousScoreLaw n (largeRelativeScoreException μ) +
          continuousScoreLaw n (badMaleSpouseScores μ)) :=
      Finset.sum_le_sum fun μ _ ↦ badStableScoreMass_le_cutoffSums μ
    _ = _ := by simp only [Finset.sum_add_distrib]
theorem tendsto_measure_badCoexposureScores_zero_of_mean_upper {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ᶠ n : ℕ in atTop,
      expectedNumStableMatchings n ≤ C * ((n : ℝ) * Real.log n)) :
    Tendsto (fun n ↦ continuousScoreLaw n (goodCoexposureScores n)ᶜ) atTop (𝓝 0) := by
  have hsmall := tendsto_sum_stable_smallSpouseScore_zero
  have hlarge := tendsto_sum_stable_largeRelativeSpouseScore_zero
  have hmale := tendsto_sum_measure_badMaleSpouseScores_zero_of_mean_upper hC hmean
  have htotal := (hsmall.add hlarge).add hmale
  simp only [add_zero] at htotal
  exact tendsto_const_nhds.squeeze' htotal (Eventually.of_forall fun _ ↦ zero_le)
    (Eventually.of_forall badScoreMass_le_cutoffSums)
end StepA3
end

-- PivotSpouseBandRegularity
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
theorem splitScorePairs_mem_pivotBaseDiagonalBand {n : ℕ} {x : ScoreProfile n}
    (μ : Matching n) (hunit : ∀ row i, x row i ∈ Ioo (0 : ℝ) 1)
    (hgood : GoodSpouseScores x μ) (hprod : (n : ℝ) / 128 ≤
      maleSpouseTotal x μ * femaleSpouseTotal x μ)
    (hY : femaleSpouseTotal x μ ≤ (n : ℝ) ^ (2 / 5 : ℝ)) :
    (splitScorePairs μ x).1 ∈ pivotBaseDiagonalBand n := by
  let d := (splitScorePairs μ x).1
  have hm (i : Fin n) : (diagonalPairAt d i).1 = maleSpouseScore x μ i :=
    congrArg Prod.fst (diagonalPairAt_splitScorePairs μ x i)
  have hf (i : Fin n) : (diagonalPairAt d i).2 = femaleSpouseByHusband μ x i := by
    rw [diagonalPairAt_splitScorePairs, femaleSpouseByHusband, femaleSpouseScore,
      Equiv.symm_apply_apply]
  have hX' : reverseDiagonalMaleTotal d = maleSpouseTotal x μ :=
    Finset.sum_congr rfl fun i _ ↦ hm i
  have hY' : pivotDiagonalFemaleTotal d = femaleSpouseTotal x μ :=
    (Finset.sum_congr rfl fun i _ ↦ hf i).trans (femaleSpouseTotal_eq_sum_byHusband μ x).symm
  change (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) ∧
    2 ≤ pivotDiagonalFemaleTotal d ∧ pivotDiagonalFemaleTotal d ≤ (n : ℝ) ^ (2 / 5 : ℝ) ∧
    (n : ℝ) / 128 ≤ reverseDiagonalMaleTotal d * pivotDiagonalFemaleTotal d ∧
    (∀ i, (diagonalPairAt d i).2 / pivotDiagonalFemaleTotal d ≤ 12 * Real.log n / n) ∧
    ∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (pivotDiagonalFemaleTotal d - 1)
  rw [hX', hY']
  refine ⟨?_, hgood.1, hY, hprod, ?_, ?_⟩
  · intro i
    rw [diagonalPairAt_splitScorePairs]
    exact ⟨⟨(hunit (.inl i) (μ i)).1.le, (hunit (.inl i) (μ i)).2⟩,
      ⟨(hunit (.inr (μ i)) i).1.le, (hunit (.inr (μ i)) i).2⟩⟩
  · intro i
    rw [hf]
    exact hgood.2.1 (μ i)
  · intro i
    rw [hm]
    exact hgood.2.2 i
private def rankStableSmallFemaleTotalEvent (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
    femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
private def rankStableBadPivotMaskEvent (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
    let z := splitScorePairs μ x
    z.1 ∈ pivotBaseDiagonalBand n ∧ z.2 ∈ badForwardMask z.1 ((n : ℝ) ^ (-11 / 20 : ℝ))}
theorem eventually_measure_rankStableSmallFemaleTotalEvent_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (rankStableSmallFemaleTotalEvent n) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_sum_stable_smallSpouseTotalLog_le p] with n h
  let E (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
  have hsub : rankStableSmallFemaleTotalEvent n ≤ᵐ[continuousScoreLaw n] ⋃ μ, E μ := by
    filter_upwards [ae_injective_rows n] with x hx hbad
    obtain ⟨μ, hμ, hY⟩ := hbad
    exact Set.mem_iUnion.mpr ⟨μ, (isStable_profileOfScores_iff hx μ).mp hμ, hY⟩
  refine (measure_mono_ae hsub).trans ((measure_iUnion_le _).trans ?_)
  rw [tsum_fintype]
  exact h
theorem eventually_measure_rankStableBadPivotMaskEvent_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (rankStableBadPivotMaskEvent n) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_sum_measure_badForwardMaskAnchorEvent_on_pivotBaseDiagonalBand_le
      (p + 2), eventually_expectedNumStableMatchings_le_sizeSq,
      eventually_gt_atTop (0 : ℕ)] with n h hm hn
  let E (μ : Matching n) := badForwardMaskAnchorEvent μ (pivotBaseDiagonalBand n)
    ((n : ℝ) ^ (-11 / 20 : ℝ))
  have hsub : rankStableBadPivotMaskEvent n ≤ᵐ[continuousScoreLaw n] ⋃ μ, E μ := by
    filter_upwards [ae_injective_rows n] with x hx hbad
    obtain ⟨μ, hμ, hd, hb⟩ := hbad
    exact Set.mem_iUnion.mpr ⟨μ, (isStable_profileOfScores_iff hx μ).mp hμ, hd, hb⟩
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  refine (measure_mono_ae hsub).trans ((measure_iUnion_le _).trans ?_)
  rw [tsum_fintype]
  refine h.trans ?_
  calc
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (2 : ℕ)) * ENNReal.ofReal ((n : ℝ) ^ (-(p + 2))) :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal hm) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_two, ← Real.rpow_add hn₀,
        show (2 : ℝ) + -(p + 2) = -p by ring]
private def goodPivotBaseGeometry (n : ℕ) : Set (ScoreProfile n) :=
  {x | x ∈ goodCoexposureScores n ∧
    (∀ μ : Matching n, IsStable (profileOfScores x) μ →
      (9 / 10 : ℝ) * Real.log n ≤ femaleSpouseTotal x μ ∧
      (n : ℝ) / 128 ≤ maleSpouseTotal x μ * femaleSpouseTotal x μ) ∧
    ∀ μ : Matching n, IsStable (profileOfScores x) μ →
      femaleSpouseTotal x μ ≤ (n : ℝ) ^ (2 / 5 : ℝ) →
      let z := splitScorePairs μ x
      z.1 ∈ pivotBaseDiagonalBand n ∧ z.2 ∉ badForwardMask z.1 ((n : ℝ) ^ (-11 / 20 : ℝ))}
private def rankStableSmallSpouseProductEvent (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
    maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128}
private theorem badPivotBaseGeometry_subset (n : ℕ) :
    (goodPivotBaseGeometry n)ᶜ ⊆
      (((goodCoexposureScores n)ᶜ ∪ rankStableSmallFemaleTotalEvent n) ∪
        rankStableSmallSpouseProductEvent n) ∪ rankStableBadPivotMaskEvent n := by
  intro x hx
  by_cases hc : x ∈ goodCoexposureScores n
  · by_cases hsmall : x ∈ rankStableSmallFemaleTotalEvent n
    · exact Or.inl (Or.inl (Or.inr hsmall))
    · by_cases hprod : x ∈ rankStableSmallSpouseProductEvent n
      · exact Or.inl (Or.inr hprod)
      · by_cases hmask : x ∈ rankStableBadPivotMaskEvent n
        · exact Or.inr hmask
        · exfalso
          apply hx
          have hprod' (μ : Matching n) (hμ : IsStable (profileOfScores x) μ) :
              (n : ℝ) / 128 ≤ maleSpouseTotal x μ * femaleSpouseTotal x μ :=
            le_of_not_gt fun h ↦ hprod ⟨μ, hμ, h⟩
          refine ⟨hc, fun μ hμ ↦ ⟨le_of_not_gt (fun h ↦ hsmall ⟨μ, hμ, h⟩),
            hprod' μ hμ⟩, ?_⟩
          intro μ hμ hY
          have hd := splitScorePairs_mem_pivotBaseDiagonalBand μ hc.2.1 (hc.2.2 μ hμ)
            (hprod' μ hμ) hY
          exact ⟨hd, fun h ↦ hmask ⟨μ, hμ, hd, h⟩⟩
  · exact Or.inl (Or.inl (Or.inl hc))
theorem tendsto_measure_badPivotBaseGeometry_zero :
    Tendsto (fun n ↦ continuousScoreLaw n (goodPivotBaseGeometry n)ᶜ) atTop (𝓝 0) := by
  have hcoex := tendsto_measure_badCoexposureScores_zero_of_mean_upper
    meanUpperConstant_nonneg eventually_expectedNumStableMatchings_le_meanUpper
  have hrate : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
    simp only [Real.rpow_neg_one]
    simpa only [ENNReal.ofReal_zero, one_div] using
      ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hzero {f : ℕ → ℝ≥0∞}
      (h : ∀ᶠ n in atTop, f n ≤ ENNReal.ofReal ((n : ℝ) ^ (-(1 : ℝ)))) :
      Tendsto f atTop (𝓝 0) :=
    tendsto_const_nhds.squeeze' hrate (Eventually.of_forall fun _ ↦ zero_le) h
  have hsmall := hzero (eventually_measure_rankStableSmallFemaleTotalEvent_le 1)
  have hprod := hzero (eventually_measure_exists_stable_smallSpouseProduct_le 1)
  have hmask := hzero (eventually_measure_rankStableBadPivotMaskEvent_le 1)
  have hmajor := ((hcoex.add hsmall).add hprod).add hmask
  simp only [add_zero] at hmajor
  refine tendsto_const_nhds.squeeze' hmajor (Eventually.of_forall fun _ ↦ zero_le) ?_
  exact Eventually.of_forall fun n ↦ (measure_mono (badPivotBaseGeometry_subset n)).trans
    ((measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl))
end StepA3
end

-- PivotSpouseSquareRegularity
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
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
private def badMaleSpouseSquareMark {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ spouseAngle (fun i ↦ maleSpouseScore x μ i) ∈
    largeSpouseAngularSquareSet n}
theorem measure_badMaleSpouseSquareMark_eq_female {n : ℕ} (μ : Matching n) :
    continuousScoreLaw n (badMaleSpouseSquareMark μ) =
      continuousScoreLaw n (badFemaleSpouseSquareMark μ.symm) := by
  let S := (spouseAngle : (Fin n → ℝ) → (Fin n → ℝ)) ⁻¹' largeSpouseAngularSquareSet n
  have hS : MeasurableSet S := (measurableSet_largeSpouseAngularSquareSet n).preimage
    (measurable_spouseAngle n)
  exact scoreStable_maleSpouseStatistic_measure_eq_female μ hS fun v e ↦ by
    change (24 < pittelAngularSquareScore (spouseAngle (v ∘ e))) ↔
      24 < pittelAngularSquareScore (spouseAngle v)
    rw [pittelAngularSquareScore_spouseAngle_comp_equiv]
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
theorem eventually_sum_measure_badMaleSpouseSquareMark_le (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n (badMaleSpouseSquareMark μ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_sum_measure_badFemaleSpouseSquareMark_le p hp] with n h
  let e : Matching n ≃ Matching n := ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩
  simp_rw [measure_badMaleSpouseSquareMark_eq_female]
  exact (Equiv.sum_comp e (fun μ ↦ continuousScoreLaw n (badFemaleSpouseSquareMark μ))).le.trans h
private def goodSpouseSquareWeights (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∀ μ : Matching n, IsStable (profileOfScores x) μ →
    pittelAngularSquareScore (spouseAngle (fun i ↦ maleSpouseScore x μ i)) ≤ 24 ∧
    pittelAngularSquareScore (spouseAngle (femaleSpouseByHusband μ x)) ≤ 24}
theorem eventually_measure_badSpouseSquareWeights_le (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n (goodSpouseSquareWeights n)ᶜ ≤
      ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_sum_measure_badMaleSpouseSquareMark_le (p + 1) (by positivity),
    eventually_sum_measure_badFemaleSpouseSquareMark_le (p + 1) (by positivity),
    eventually_ge_atTop (2 : ℕ)] with n hm hf hn
  let M := ⋃ μ : Matching n, badMaleSpouseSquareMark μ
  let F := ⋃ μ : Matching n, badFemaleSpouseSquareMark μ
  let U : Set (ScoreProfile n) := M ∪ F
  have hsub : (goodSpouseSquareWeights n)ᶜ ≤ᵐ[continuousScoreLaw n] U := by
    filter_upwards [ae_injective_rows n] with x hx hbad
    by_contra hnot
    apply hbad
    intro μ hμ
    have hs := (isStable_profileOfScores_iff hx μ).mp hμ
    exact ⟨le_of_not_gt fun h ↦ hnot (Or.inl (mem_iUnion.mpr ⟨μ, hs, h⟩)),
      le_of_not_gt fun h ↦ hnot (Or.inr (mem_iUnion.mpr ⟨μ, hs, h⟩))⟩
  have hn' : 0 < n := by omega
  have hn₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ (n : ℝ) ^ (-(p + 1)) := Real.rpow_nonneg (by positivity) _
  have hM : continuousScoreLaw n M ≤ ENNReal.ofReal ((n : ℝ) ^ (-(p + 1))) :=
    (measure_iUnion_le _).trans (by rwa [tsum_fintype])
  have hF : continuousScoreLaw n F ≤ ENNReal.ofReal ((n : ℝ) ^ (-(p + 1))) :=
    (measure_iUnion_le _).trans (by rwa [tsum_fintype])
  calc
    _ ≤ continuousScoreLaw n M + continuousScoreLaw n F :=
      (measure_mono_ae hsub).trans (measure_union_le M F)
    _ ≤ _ := (add_le_add hM hF).trans (by
      rw [← ENNReal.ofReal_add ha ha]
      apply ENNReal.ofReal_le_ofReal
      exact (two_mul _).symm.le.trans
        ((mul_le_mul_of_nonneg_right hn₂ ha).trans_eq (size_mul_neg_rpow_shift hn' p)))
private def goodPivotScoreGeometry (n : ℕ) : Set (ScoreProfile n) :=
  goodPivotBaseGeometry n ∩ goodSpouseSquareWeights n
theorem tendsto_measure_badPivotScoreGeometry_zero :
    Tendsto (fun n ↦ continuousScoreLaw n (goodPivotScoreGeometry n)ᶜ) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
    simp only [Real.rpow_neg_one]
    simpa only [ENNReal.ofReal_zero, one_div] using
      ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hs : Tendsto (fun n ↦ continuousScoreLaw n (goodSpouseSquareWeights n)ᶜ)
      atTop (𝓝 0) :=
    tendsto_const_nhds.squeeze' hr (Eventually.of_forall fun _ ↦ zero_le)
      (eventually_measure_badSpouseSquareWeights_le 1 (by norm_num))
  have hmajor := tendsto_measure_badPivotBaseGeometry_zero.add hs
  simp only [add_zero] at hmajor
  refine tendsto_const_nhds.squeeze' hmajor (Eventually.of_forall fun _ ↦ zero_le) ?_
  exact Eventually.of_forall fun n ↦ by
    rw [goodPivotScoreGeometry, compl_inter]
    exact measure_union_le _ _
end StepA3
end

-- ForestDeterministic
section
open scoped BigOperators Classical
namespace StepA3
end StepA3
end

-- ForestProductProbability
section
open scoped BigOperators Classical
namespace StepA3
end StepA3
end

-- ForestRankOne
section
namespace StepA3
end StepA3
end

-- ForestRowThinning
section
open scoped BigOperators Classical
namespace StepA3
end StepA3
end

-- ForwardSuccessorRowLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- ForwardSuccessorOutcome
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- PivotForwardRowDeficit
section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
private noncomputable def forwardSpouseWeight {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).2 / ∑ j, (diagonalPairAt d j).2
end StepA3
end

-- PivotForwardForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- PivotLocalEligibility
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
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

end StepA3
end

-- PivotMarkedDecorationCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
variable {n : ℕ}
section MatchingEndpoints
variable {x : ScoreProfile n} {μ₀ μ ρ σ : Matching n}
  {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ}
end MatchingEndpoints
end StepA3
end

-- PivotRestrictedMoment
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
section ConditionalOrder
variable {Ω : Type*} {m m₀ : MeasurableSpace Ω}
end ConditionalOrder
end StepA3
end

-- PivotFullRevealLaw
section
open MeasureTheory Set StableMarriage
open scoped ENNReal
namespace StepA3
variable {n : ℕ}
end StepA3
end

-- PivotConditionalMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
variable {n : ℕ}
end StepA3
end

-- DeferredAcceptanceTranscript
section
open StableMarriage
open scoped BigOperators
namespace StepA3
namespace DAState
variable {n : ℕ}
end DAState
end StepA3
end

-- UniformStreamRanks
section
open Function MeasureTheory
open scoped ENNReal StepA3
namespace StepA3
variable {n T : ℕ}
end StepA3
end

-- AdaptiveFiniteQueries
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
variable {I A : Type*}
variable [Fintype I] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
end StepA3
end

-- DAStreamSimulation
section
open StableMarriage
namespace StepA3
namespace DAStreamState
variable {n T : ℕ}
end DAStreamState
end StepA3
end

-- DAProposalCoupon
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology StepA3
namespace StepA3
variable {n T : ℕ}
end StepA3
end

-- AdaptiveScoreRectangles
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
variable {ι : Type*}
variable [DecidableEq ι]
variable [Fintype ι]
end StepA3
end

-- UniformLogScoreMoments
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA3
section FiniteProduct
variable {ι : Type*}
variable [Fintype ι]


end FiniteProduct
end StepA3
end

-- AdaptiveScoreFiberMoments
section
open MeasureTheory Set
open scoped BigOperators ENNReal MeasureTheory
namespace StepA3
section Fiber
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
end Fiber
section Cache
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

end Cache
end StepA3
end

-- AdaptiveScoreFiberAssembly
section
open MeasureTheory Set
namespace StepA3
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

end StepA3
end

-- RotationParticipationClock
section
open StableMarriage
open scoped BigOperators
namespace StepA3
end StepA3
end

-- RotationClockCells
section
open StableMarriage
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ ν : Matching n}
variable {ρ : Equiv.Perm (Fin n)}
end StepA3
end

-- RotationSuccessorQueries
section
open StableMarriage
namespace StepA3
variable {n : ℕ}
variable {p : Profile n} {μ : Matching n} {m w : Fin n}
end StepA3
end

-- ScoreRotationWalk
section
open StableMarriage
namespace StepA3
variable {n : ℕ}
end StepA3
end

-- ScoreRotationBranchLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators Classical
namespace StepA3
variable {n : ℕ}
end StepA3
end

-- DALowerEndpoint
section
open Filter MeasureTheory Set StableMarriage
open scoped Classical ENNReal Topology
namespace StepA3
variable {n : ℕ}
end StepA3
end

-- ExponentialSpouseLogTail
section
open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
namespace StepA3
local instance : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)
end StepA3
end

-- MarkedSpouseLogGeometry
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
end StepA3
end

-- CycleSupportCount
section
open Equiv.Perm Finset
open scoped BigOperators Classical
namespace StepA3
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end StepA3
end

-- PointedSymmetricSums
section
open Finset
open scoped BigOperators
namespace StepA3
end StepA3
end

-- SingletonGaussianLength
section
open scoped BigOperators
open Finset
namespace StepA3
end StepA3
end

-- PivotSingletonLength
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- SingletonAnchorCounting
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal StepA3
namespace StepA3
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
end StepA3
end

-- ForwardRowDeficitConcentration
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- MarkedForwardRowDeficit
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
end StepA3
end

-- SingletonDiagonalExceptions
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
end StepA3
end

-- PivotSingletonMarkedLength
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- RotationLengthCutoff
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal StepA3 Topology
namespace StepA3
end StepA3
end

-- RotationClockBand
section
open Filter MeasureTheory StableMarriage
open scoped ENNReal Topology
namespace StepA3
end StepA3
end

-- ScoreRotationHistory
section
open StableMarriage
open scoped Classical
namespace StepA3
variable {n : ℕ}
end StepA3
end

-- ScoreRotationBandCrossing
section
open StableMarriage
open scoped BigOperators
namespace StepA3
variable {n : ℕ}
end StepA3
end

-- DAUpperEndpoint
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
end StepA3
end

-- ParticipationClockMartingale
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace StepA3
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {ℱ : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
end StepA3
end

-- FinitePartitionClock
section
open MeasureTheory Set
open scoped Function
namespace StepA3
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
end StepA3
end

-- ScoreClockFiltration
section
open MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepA3
variable {n : ℕ}
end StepA3
end

-- ScoreRotationBranchTest
section
open MeasureTheory Set StableMarriage
open scoped Classical
namespace StepA3
variable {n : ℕ}
end StepA3
end

-- ScoreRotationClockBudget
section
open MeasureTheory Set StableMarriage
open scoped BigOperators Classical Function
namespace StepA3
variable {n : ℕ}
end StepA3
end

-- ScoreRotationClockMaximal
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology
namespace StepA3
variable {n : ℕ}
end StepA3
end

-- ScoreRotationLengthBudgets
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology
namespace StepA3
end StepA3
end

-- ScoreRotationBandAbundance
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology
namespace StepA3
end StepA3
end

-- ScoreRotationAnchorAbundance
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology
namespace StepA3
end StepA3
end

-- ScoreRotationNonTiny
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology
namespace StepA3
end StepA3
end

-- ScoreRotationAnchorProbability
section
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace StepA3
end StepA3
end

-- DAEndpointAsymptotics
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology StepA3
namespace StepA3
end StepA3
end

-- PivotMarkedCutoffBridge
section
open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
section IndependentRows
variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
  (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
  (out : ∀ i, Ω i → Option (Fin n)) (g : ∀ i, Fin n → Ω i → ℝ)
  [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
end IndependentRows
end StepA3
end

-- PivotSupportMassTail
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology
namespace StepA3
end StepA3
end

-- PivotForwardIncrementTail
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
end StepA3
end

-- PivotEligibleAbundance
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
end StepA3
end

-- PivotAggregateMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA3
variable {n : ℕ}
end StepA3
end

-- PivotDecorationRevealInvariance
section
open MeasureTheory Set StableMarriage
namespace StepA3
variable {n : ℕ} {μ ρ σ : Matching n} {x y : ScoreProfile n}
  {flag : OffDiagonalCellIndex n → Bool}
private structure SameReverseReveal (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x y : ScoreProfile n) : Prop where
  diagonal : (splitScorePairs μ x).1 = (splitScorePairs μ y).1
  observed : forwardRevealWithColumns flag (splitScorePairs μ x).2 =
    forwardRevealWithColumns flag (splitScorePairs μ y).2
theorem SameReverseReveal.symm (h : SameReverseReveal μ flag x y) :
    SameReverseReveal μ flag y x := ⟨h.diagonal.symm, h.observed.symm⟩
end StepA3
end

-- PivotLaterRevealReplay
section
open MeasureTheory Set StableMarriage
namespace StepA3
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
end StepA3
end

-- PivotComparableCentered
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
namespace PivotCountParameters
variable {n : ℕ}
end PivotCountParameters
end StepA3
end

-- PivotTwoCycleForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA3
end StepA3
end

-- LogarithmicCutoffs
section
open Filter
open scoped Topology BigOperators
namespace StepA3
end StepA3
end

-- PivotVarianceClosure
section
open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators ENNReal Topology
namespace StepA3
namespace PivotCountParameters
variable {n : ℕ}
end PivotCountParameters
variable {n : ℕ}
namespace PivotCountParameters
end PivotCountParameters
end StepA3
end

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 30000 in
theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H1_R1.H3 :=
  ⟨@StepA3.tendsto_measure_badPivotScoreGeometry_zero, @StepA3.tendsto_measure_badCoexposureScores_zero_of_mean_upper⟩
