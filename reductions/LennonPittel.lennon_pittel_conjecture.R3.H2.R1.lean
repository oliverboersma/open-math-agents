import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R3

/-! Port of Bo Cowgill’s lower-tail criterion in bocowgill/lennon-pittel
at cf950d059659, Apache-2.0. Rank-order sampling identifies the discrete law
with independently uniform scores. A centered incidence count in score space
then suffices by the second-moment inequality. -/
-- Credit: @marcusbuffett

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology

namespace OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1
theorem measure_tail_ge_of_centeredMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {S T M : Ω → ℝ}
    (hTS : ∀ x, T x ≤ S x) (hT : Measurable T) (hM : Measurable M)
    {a d δ : ℝ} (ha : 0 < a) (hd : 0 < d) (hδ : 0 < δ) (hδ' : δ < 1)
    (hcenter : ENNReal.ofReal (1 - δ / 2) ≤ μ {x | d * a ≤ M x})
    (hmoment : (∫⁻ x, ENNReal.ofReal (((T x - M x) / a) ^ 2) ∂μ) ≤ ENNReal.ofReal ((δ / 2) * (d / 2) ^ 2)) :
    ENNReal.ofReal (1 - δ) ≤ μ {x | (d / 2) * a ≤ S x} := by
  let f (x : Ω) := ENNReal.ofReal (((T x - M x) / a) ^ 2)
  let G := {x | (d / 2) * a ≤ S x}
  let E := {x | ENNReal.ofReal ((d / 2) ^ 2) ≤ f x}
  have hf : Measurable f := by unfold f; fun_prop
  have hpos : 0 < (d / 2) ^ 2 := by positivity
  have hE : μ E ≤ ENNReal.ofReal (δ / 2) := by
    calc
      _ ≤ (∫⁻ x, ENNReal.ofReal (((T x - M x) / a) ^ 2) ∂μ) / ENNReal.ofReal ((d / 2) ^ 2) :=
        meas_ge_le_lintegral_div hf.aemeasurable (ENNReal.ofReal_pos.mpr hpos).ne'
          ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((δ / 2) * (d / 2) ^ 2) / ENNReal.ofReal ((d / 2) ^ 2) :=
        ENNReal.div_le_div_right hmoment _
      _ = _ := by
        rw [← ENNReal.ofReal_div_of_pos hpos, mul_div_cancel_right₀ _ hpos.ne']
  have hcover : {x | d * a ≤ M x} ⊆ G ∪ E := by
    intro x hx
    by_cases hg : x ∈ G
    · exact Or.inl hg
    · right
      have hs : S x < (d / 2) * a := lt_of_not_ge hg
      have hdif : (T x - M x) / a ≤ -(d / 2) := by
        apply (div_le_iff₀ ha).2
        linarith [hTS x, (show d * a ≤ M x from hx)]
      apply ENNReal.ofReal_le_ofReal
      calc
        (d / 2) ^ 2 ≤ (-((T x - M x) / a)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = _ := by ring
  have hbound : ENNReal.ofReal (1 - δ / 2) ≤ μ G + ENNReal.ofReal (δ / 2) :=
    hcenter.trans ((measure_mono hcover).trans
      ((measure_union_le G E).trans (add_le_add le_rfl hE)))
  have hfin := measure_ne_top μ G
  have hR := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.ofReal_ne_top⟩) hbound
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - δ / 2),
    ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ δ / 2)] at hR
  change ENNReal.ofReal (1 - δ) ≤ μ G
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal (by linarith)


/-- The finite rank model and independent continuous scores give the same count tails. -/
def H1 : Prop :=
  let Ω (n : ℕ) := (Fin n ⊕ Fin n) → Fin n → ℝ
  let μ (n : ℕ) : Measure (Ω n) := Measure.pi fun _ : Fin n ⊕ Fin n ↦
    Measure.pi fun _ : Fin n ↦ volume.restrict (Icc (0 : ℝ) 1)
  let S (n : ℕ) (x : Ω n) := Nat.card {m : Matching n // ∀ i j, ¬
    (m i ≠ j ∧ x (.inl i) j < x (.inl i) (m i) ∧ x (.inr j) i < x (.inr j) (m.symm j))}
  ∀ n : ℕ, ∀ t : ℝ, μ n {x | t ≤ (S n x : ℝ)} =
    (uniformProfile n).toMeasure {p | t ≤ (numStableMatchings p : ℝ)}

/-- A score-space subcount with a large center and small normalized squared deviation. -/
def H2 : Prop :=
  let Ω (n : ℕ) := (Fin n ⊕ Fin n) → Fin n → ℝ
  let μ (n : ℕ) : Measure (Ω n) := Measure.pi fun _ : Fin n ⊕ Fin n ↦
    Measure.pi fun _ : Fin n ↦ volume.restrict (Icc (0 : ℝ) 1)
  let S (n : ℕ) (x : Ω n) := Nat.card {m : Matching n // ∀ i j, ¬
    (m i ≠ j ∧ x (.inl i) j < x (.inl i) (m i) ∧ x (.inr j) i < x (.inr j) (m.symm j))}
  ∀ η : ℝ, 0 < η → ∃ d : ℝ, 0 < d ∧ ∀ e : ℝ, 0 < e →
    ∃ T M : ∀ n : ℕ, Ω n → ℝ, (∀ n, Measurable (T n)) ∧ (∀ n, Measurable (M n)) ∧
      (∀ n x, T n x ≤ (S n x : ℝ)) ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (1 - η) ≤ μ n {x | d * ((n : ℝ) * Real.log n) ≤ M n x} ∧
      (∫⁻ x, ENNReal.ofReal (((T n x - M n x) / ((n : ℝ) * Real.log n)) ^ 2) ∂(μ n))
        ≤ ENNReal.ofReal e

theorem main : H1 → H2 → OMA.R_LennonPittel_lennon_pittel_conjecture_R3.H2 := by
  intro law cert δ hδ
  by_cases hδ' : δ < 1
  · obtain ⟨d, hd, hclose⟩ := cert (δ / 2) (by positivity)
    obtain ⟨T, M, hT, hM, hTS, hclose⟩ := hclose ((δ / 2) * (d / 2) ^ 2) (by positivity)
    refine ⟨d / 2, by positivity, ?_⟩
    filter_upwards [hclose, eventually_gt_atTop (1 : ℕ)] with n hn hn'
    have hpos : (1 : ℝ) < n := by exact_mod_cast hn'
    have ha : 0 < (n : ℝ) * Real.log n := mul_pos (by linarith) (Real.log_pos hpos)
    let μ := Measure.pi fun _ : Fin n ⊕ Fin n ↦
      Measure.pi fun _ : Fin n ↦ volume.restrict (Icc (0 : ℝ) 1)
    letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨by simp [Real.volume_Icc]⟩
    rw [← law n ((d / 2) * ((n : ℝ) * Real.log n))]
    exact measure_tail_ge_of_centeredMoment μ (hTS n) (hT n) (hM n) ha hd hδ hδ' hn.1 hn.2
  · refine ⟨1, one_pos, Eventually.of_forall fun n ↦ ?_⟩
    rw [ENNReal.ofReal_eq_zero.mpr (by linarith : 1 - δ ≤ 0)]
    exact zero_le

end OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1
