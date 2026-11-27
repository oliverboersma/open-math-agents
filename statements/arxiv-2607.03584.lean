import Mathlib

/-!
Source: https://arxiv.org/abs/2607.03584 (Mora Cuellar, Iosevich, Kulkarni,
Rojas Aravena and Yavicoli). This is the named question about the dyadic set
itself, not the paper's theorem about adding another infinite set.
Credit: @my-other-github-account
-/
namespace OMA.S_arxiv_2607_03584

theorem main : ∃ E : Set ℝ, MeasurableSet E ∧ 0 < MeasureTheory.volume E ∧
    ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x + s * ((2 : ℝ)⁻¹ ^ n) ∉ E := by
  sorry

end OMA.S_arxiv_2607_03584
