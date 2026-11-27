import Mathlib

/-!
# 1/3–2/3 conjecture

Source: https://en.wikipedia.org/wiki/1/3–2/3_conjecture
Credit: @grp06

Every finite partial order that is not total has a pair whose relative order has
probability between 1/3 and 2/3, inclusive, in a uniform random linear extension.
A linear extension is represented by its bijective rank function into `Fin (Fintype.card P)`.
-/

namespace OMA.S_wp_1_3_2_3_conjecture

theorem main :
    ∀ (P : Type*) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    let extensions : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let before := (extensions.filter (fun rank => rank x < rank y)).card
      let prob : ℚ := (before : ℚ) / (extensions.card : ℚ)
      1 / 3 ≤ prob ∧ prob ≤ 2 / 3 := by
  sorry

end OMA.S_wp_1_3_2_3_conjecture
