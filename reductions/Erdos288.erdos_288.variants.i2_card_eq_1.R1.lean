import FormalConjectures.ErdosProblems.«288»

/-!
An integer translate of a unit fraction has that unit fraction's reduced
denominator. This removes the singleton from the search. The remaining
condition tests the reduced numerator of the interval sum against −1.
See the [Erdős Problems discussion of the singleton case](https://www.erdosproblems.com/forum/thread/288).
-/

namespace OMA.R_Erdos288_erdos_288_variants_i2_card_eq_1_R1

/-- Characterize when adding a unit fraction to a rational gives an integer. -/
def H1 : Prop :=
  ∀ (r : ℚ) (d : ℕ+),
    (∃ z : ℤ, r + (d⁻¹ : ℚ) = z) ↔
      r.den = (d : ℕ) ∧ (r.den : ℤ) ∣ r.num + 1

/-- The remaining finiteness question over endpoints alone. -/
def H2 : Prop :=
  Set.Finite {I : ℕ+ × ℕ+ | I.1 ≤ I.2 ∧
    let r := ∑ i ∈ Set.Icc I.1 I.2, (i⁻¹ : ℚ)
    (r.den : ℤ) ∣ r.num + 1}

section Proof

theorem main : H1 → H2 → type_of% @Erdos288.erdos_288.variants.i2_card_eq_1 := by
  intro criterion finiteIntervals
  let r (I : ℕ+ × ℕ+) : ℚ := ∑ i ∈ Set.Icc I.1 I.2, (i⁻¹ : ℚ)
  let recover (I : ℕ+ × ℕ+) : (ℕ+ × ℕ+) × ℕ+ :=
    (I, ⟨(r I).den, (r I).den_pos⟩)
  refine (finiteIntervals.image recover).subset ?_
  rintro ⟨I, d⟩ ⟨hI, n, hn⟩
  have hz : ∃ z : ℤ, r I + (d⁻¹ : ℚ) = z := by
    refine ⟨((n : ℕ) : ℤ), ?_⟩
    simpa [r] using hn
  obtain ⟨hd, hdvd⟩ := (criterion (r I) d).mp hz
  exact ⟨I, ⟨hI, hdvd⟩, Prod.ext rfl (Subtype.ext hd)⟩

end Proof

end OMA.R_Erdos288_erdos_288_variants_i2_card_eq_1_R1
