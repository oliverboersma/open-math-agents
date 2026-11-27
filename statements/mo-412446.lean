import Mathlib

/-!
# MathOverflow 412446

Source: https://mathoverflow.net/questions/412446
-/

namespace OMA.S_mo_412446

open Finset

noncomputable def boltzmann {n : ℕ} (E : Fin n → ℝ) (β : ℝ)
    (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  Real.exp (-β * E i) / ∑ j ∈ S, Real.exp (-β * E j)

theorem main : ∀ (n : ℕ) (E : Fin n → ℝ) (β : ℝ) (S : Finset (Fin n)),
    S.Nonempty → S ≠ univ →
    (∏ i, boltzmann E β univ i) < ∏ i ∈ S, boltzmann E β S i := by
  sorry

end OMA.S_mo_412446
