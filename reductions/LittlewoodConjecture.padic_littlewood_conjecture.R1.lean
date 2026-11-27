import FormalConjectures.Wikipedia.LittlewoodConjecture

-- Reduction LittlewoodConjecture.padic_littlewood_conjecture.R1 of the p-adic Littlewood conjecture
-- (liminf formulation)
-- Credit: @marcusbuffett

/-!
# The p-adic Littlewood conjecture (liminf form) is only open for badly approximable numbers

The conjecture says `liminf n * |n|_p * ‖nα‖ = 0` for every real `α` and prime `p`, where `‖x‖`
is the distance to the nearest integer.

* `H1` (classical remark): if `n ‖nα‖` is arbitrarily small for infinitely many `n` (`α` is not
  badly approximable), the liminf is `0`, because `|n|_p ≤ 1` and all terms are nonnegative.
* `H2`: the conjecture when `n ‖nα‖ ≥ ε` for all large `n` (`α` badly approximable). This is
  the open part.
-/

namespace OMA.R_LittlewoodConjecture_padic_littlewood_conjecture_R1

open Filter

/-- The case of an `α` that is not badly approximable. -/
def H1 : Prop :=
  ∀ (α : ℝ) (p : ℕ), p.Prime →
    (∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, n * distToNearestInt (n * α) < ε) →
    atTop.liminf (fun (n : ℕ) ↦ n * padicNorm p n * distToNearestInt (n * α)) = 0

/-- The open part: badly approximable `α`. -/
def H2 : Prop :=
  ∀ (α : ℝ) (p : ℕ), p.Prime →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, ε ≤ n * distToNearestInt (n * α)) →
    atTop.liminf (fun (n : ℕ) ↦ n * padicNorm p n * distToNearestInt (n * α)) = 0

theorem main : H1 → H2 → type_of% @LittlewoodConjecture.padic_littlewood_conjecture := by
  intro h1 h2 α p hp
  by_cases h : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, n * distToNearestInt (n * α) < ε
  · exact h1 α p hp h
  · apply h2 α p hp
    push Not at h
    obtain ⟨ε, hε, hn⟩ := h
    exact ⟨ε, hε, hn⟩

end OMA.R_LittlewoodConjecture_padic_littlewood_conjecture_R1
