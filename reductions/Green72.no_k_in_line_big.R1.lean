import FormalConjectures.GreensOpenProblems.«72»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Green72_no_k_in_line_big_R1
open Finset Green72

/-- The large-parameter grid packing theorem of Grebennikov and Kwan,
stated as integer line incidence bounds. -/
def H1 : Prop := ∀ (k N : ℕ), 10 ^ 37 < k → k ≤ N →
  ∃ s ⊆ (range N ×ˢ range N), s.card = (k - 1) * N ∧ (∀ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) → -(N : ℤ) < a → a < N → -(N : ℤ) < b → b < N →
    (s.filter (fun i ↦ a * i.1 + b * i.2 = c)).card ≤ k - 1)

/-- Bounded integer line tests certify avoidance of real collinear subsets. -/
def H2 : Prop := ∀ (k N : ℕ) (s : Finset (ℕ × ℕ)), 2 ≤ k →
  s ⊆ (range N ×ˢ range N) → (∀ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) → -(N : ℤ) < a → a < N → -(N : ℤ) < b → b < N →
    (s.filter (fun i ↦ a * i.1 + b * i.2 = c)).card ≤ k - 1) → AllowedSet k N s

theorem main : H1 → H2 → type_of% @Green72.no_k_in_line_big := by
  intro pack certify k N hk hN
  obtain ⟨s,hs,hc,hl⟩ := pack k N hk hN
  refine le_antisymm allowedSetSize_le ?_
  change (k - 1) * N ≤ sSup {r | ∃ t, r = t.card ∧ AllowedSet k N t}
  apply le_csSup
  · refine ⟨(range N ×ˢ range N).card, ?_⟩
    rintro r ⟨t,rfl,ht⟩
    exact card_le_card fun i hi ↦ mem_product.mpr
      ⟨mem_range.mpr (ht.is_bounded i hi).1, mem_range.mpr (ht.is_bounded i hi).2⟩
  · exact ⟨s,hc.symm,certify k N s (by omega) hs hl⟩

end OMA.R_Green72_no_k_in_line_big_R1
