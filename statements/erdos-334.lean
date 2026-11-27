import Mathlib

/-!
# Erdős Problem 334

Source: https://www.erdosproblems.com/334
Credit: @jeonbik

State the problem EXACTLY as the source states it: same quantifiers, same ranges,
no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_erdos_334

def IsSmooth (t m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ≤ t

noncomputable def bestSmoothBound (n : ℕ) : ℕ :=
  sInf { t : ℕ | ∃ a b : ℕ, a + b = n ∧ IsSmooth t a ∧ IsSmooth t b }

theorem main : ∀ k : ℕ, 1 ≤ k → ∀ᶠ n in Filter.atTop,
    (bestSmoothBound n) ^ k ≤ n := by
  sorry

end OMA.S_erdos_334
