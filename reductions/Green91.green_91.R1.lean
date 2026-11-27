import FormalConjectures.GreensOpenProblems.«91»
import Mathlib

/-! Friendly bisections of G(n, 1/2) with 99 percent friendly vertices, from the theorem of
Ferber, Kwan, Narayanan, Sah and Sawhney, Friendly bisections of random graphs (2022): with
probability tending to 1 there is a bisection in which all but o(n) vertices are friendly.
This is the catalogue's Green91.green_91.variants.fknss. The remaining step is that an o(n)
error is eventually at most n / 100; the passage to the probabilities is monotonicity of the
measure. -/

namespace OMA.R_Green91_green_91_R1
open Filter Asymptotics Topology

/-- The theorem of Ferber, Kwan, Narayanan, Sah and Sawhney. -/
def H1 : Prop := ∃ f : ℕ → ℝ, f =o[atTop] (fun n : ℕ ↦ (n : ℝ)) ∧
  Tendsto (fun n : ℕ ↦ Green91.prob n fun G ↦
    ∃ s : Finset (Fin n), s.card = n / 2 ∧ (n : ℝ) - f n ≤ Green91.numFriendly G s)
    atTop (𝓝 1)

/-- An o(n) error is eventually at most n / 100. -/
def H2 : Prop := ∀ f : ℕ → ℝ, f =o[atTop] (fun n : ℕ ↦ (n : ℝ)) →
  ∀ᶠ n : ℕ in atTop, (99 / 100 : ℝ) * n ≤ (n : ℝ) - f n

theorem main : H1 → H2 → type_of% @Green91.green_91 := by
  rintro ⟨f, hf, ht⟩ h2
  have hev := h2 f hf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ht tendsto_const_nhds ?_ ?_
  · filter_upwards [hev] with n hn
    exact MeasureTheory.measure_mono (fun G ⟨s, hs, h⟩ => ⟨s, hs, hn.trans h⟩)
  · exact Eventually.of_forall fun n => MeasureTheory.prob_le_one

end OMA.R_Green91_green_91_R1
