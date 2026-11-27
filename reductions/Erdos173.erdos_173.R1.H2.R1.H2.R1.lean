import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1

/-! Port of Jacob Parish (Plasma AI), plasma-ai/erdos-173 at 4a368a652753,
including the measurable-representative argument adapted from OpenAI,
openai/math at adc7f124. Both are used under Apache-2.0.
The L² field encodes avoidance through a quadratic identity. A jointly
measurable version allows Tonelli to select a single avoiding coloring. -/
-- Credit: @marcusbuffett

open MeasureTheory
open scoped ENNReal

namespace OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1

def H1 : Prop :=
  let ζ : ℂ := ⟨1 / 2, √3 / 2⟩
  let avoids (c : ℂ → Fin 2) (r : ℝ) := ∀ p u : ℂ, ‖u‖ = 1 →
    ¬ (c (p + u * r) = c p ∧ c (p + u * (r * ζ)) = c p)
  ∀ x : ℝ, 2 / 3 < x → x < 3 / 2 → x ≠ 1 → ∀ c : ℂ → Fin 2,
    avoids c 1 → avoids c x →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (ν : Measure Ω), IsProbabilityMeasure ν ∧
      ∃ f : ℂ → Lp ℂ 2 ν, Continuous f ∧ ∀ r : ℝ, (r = 1 ∨ r = x) →
        ∀ p : ℂ, ∀ u : Circle, ∀ᵐ ω ∂ν,
          let a := (f p ω).re
          let b := (f (p + u * r) ω).re
          let d := (f (p + u * (r * ζ)) ω).re
          1 + a * b + a * d + b * d = 0

def H2 : Prop := ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (f : ℂ → Lp ℂ 2 ν),
  Continuous f → ∃ F : ℂ × Ω → ℂ, Measurable F ∧
    ∀ p : ℂ, (fun ω => F (p, ω)) =ᵐ[ν] f p

private theorem two_signs {a b d : ℝ} (h : 1 + a * b + a * d + b * d = 0) :
    let color (z : ℝ) : Fin 2 := if 0 ≤ z then 0 else 1
    ¬ (color b = color a ∧ color d = color a) := by
  dsimp
  intro ⟨hb, hd⟩
  by_cases ha : 0 ≤ a <;> by_cases hb' : 0 ≤ b <;> by_cases hd' : 0 ≤ d <;>
    simp [ha, hb', hd'] at hb hd
  · nlinarith [mul_nonneg ha hb', mul_nonneg ha hd', mul_nonneg hb' hd']
  · have ha' : a < 0 := lt_of_not_ge ha
    have hb'' : b < 0 := lt_of_not_ge hb'
    have hd'' : d < 0 := lt_of_not_ge hd'
    nlinarith [mul_pos_of_neg_of_neg ha' hb'', mul_pos_of_neg_of_neg ha' hd'',
      mul_pos_of_neg_of_neg hb'' hd'']

theorem main : H1 → H2 → OMA.R_Erdos173_erdos_173_R1_H2_R1.H2 := by
  intro field representative x hlow hhigh hne c h₁ h₂
  obtain ⟨Ω, mΩ, ν, hν, f, hf, hrel⟩ := field x hlow hhigh hne c h₁ h₂
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure ν := hν
  obtain ⟨F, hF, hversion⟩ := representative Ω ν f hf
  let ζ : ℂ := ⟨1 / 2, √3 / 2⟩
  let color (t : ℝ) : Fin 2 := if 0 ≤ t then 0 else 1
  let col (z : ℂ × Ω) := color (F z).re
  have hcolor : Measurable color := Measurable.ite measurableSet_Ici measurable_const measurable_const
  have hcol : Measurable col := hcolor.comp (Complex.measurable_re.comp hF)
  let Ang := AddCircle (2 * Real.pi)
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let M := (volume : Measure ℂ).prod (AddCircle.haarAddCircle : Measure Ang)
  let mono (r : ℝ) (q : (ℂ × Ang) × Ω) :=
    let u : ℂ := AddCircle.toCircle q.1.2
    col (q.1.1 + u * r, q.2) = col (q.1.1, q.2) ∧
      col (q.1.1 + u * (r * ζ), q.2) = col (q.1.1, q.2)
  have hm (r : ℝ) : MeasurableSet {q | ¬ mono r q} := by
    have hp : Measurable fun q : (ℂ × Ang) × Ω => q.1.1 := measurable_fst.fst
    have hu : Measurable fun q : (ℂ × Ang) × Ω => (AddCircle.toCircle q.1.2 : ℂ) :=
      (continuous_subtype_val.comp AddCircle.continuous_toCircle).measurable.comp measurable_fst.snd
    have h0 := hcol.comp (hp.prodMk measurable_snd)
    have h1 := hcol.comp ((hp.add (hu.mul_const (r : ℂ))).prodMk measurable_snd)
    have h2 := hcol.comp ((hp.add (hu.mul_const ((r : ℂ) * ζ))).prodMk measurable_snd)
    exact ((measurableSet_eq_fun h1 h0).inter (measurableSet_eq_fun h2 h0)).compl
  have ha (q : ℂ × Ang) (r : ℝ) (hr : r = 1 ∨ r = x) : ∀ᵐ ω ∂ν, ¬ mono r (q,ω) := by
    let u := AddCircle.toCircle q.2
    filter_upwards [hrel r hr q.1 u, hversion q.1, hversion (q.1 + u * r),
        hversion (q.1 + u * (r * ζ))] with ω hq h0 h1 h2
    change ¬ (color (F (_,ω)).re = color (F (_,ω)).re ∧ color (F (_,ω)).re = color (F (_,ω)).re)
    change F (_,ω) = _ at h0 h1 h2
    rw [h0, h1, h2]
    exact two_signs hq
  have hmBoth : MeasurableSet {q : (ℂ × Ang) × Ω | ¬ mono 1 q ∧ ¬ mono x q} := (hm 1).inter (hm x)
  have ht := (Measure.ae_ae_comm (μ := M) (ν := ν) hmBoth).mp
    (Filter.Eventually.of_forall fun q => (ha q 1 (Or.inl rfl)).and (ha q x (Or.inr rfl)))
  obtain ⟨ω, hω⟩ := ht.exists
  exact ⟨fun z => col (z,ω), hcol.comp (measurable_id.prodMk measurable_const),
    hω.mono fun _ h => h.1, hω.mono fun _ h => h.2⟩

end OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1

