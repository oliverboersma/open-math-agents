import FormalConjectures.Paper.LatinSquare
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1
open LatinSquare

/-- The enumeration in orders seven and nine, after fixing the first row and column. -/
def H1 : Prop := ∀ (n : ℕ) [NeZero n], n ∈ ({7,9} : Finset ℕ) → ∀ L : LatinSquare n,
  (∀ i, L.mat 0 i = i) → (∀ i, L.mat i 0 = i) → ∃ σ, IsTransversal L σ

/-- Exhaustive base cases up to order five in the same normalization. -/
def H2 : Prop := ∀ (n : ℕ) [NeZero n], n ∈ ({1,3,5} : Finset ℕ) → ∀ L : LatinSquare n,
  (∀ i, L.mat 0 i = i) → (∀ i, L.mat i 0 = i) → ∃ σ, IsTransversal L σ

/-- Reindexing rows and columns normalizes any Latin square and transports transversals back. -/
def H3 : Prop := ∀ (n : ℕ) [NeZero n] (L : LatinSquare n), ∃ M : LatinSquare n,
  (∀ i, M.mat 0 i = i) ∧ (∀ i, M.mat i 0 = i) ∧
  ((∃ σ, IsTransversal M σ) → ∃ σ, IsTransversal L σ)

theorem main : H1 → H2 → H3 → type_of% @LatinSquare.oddOrderLeq9LatinSquareTransversal := by
  intro large small normalize n hn ho L
  obtain ⟨k,hk⟩ := ho
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨M,hr,hc,pull⟩ := normalize n L
  apply pull
  by_cases h : n ≤ 5
  · apply small n _ M hr hc
    simp; omega
  · apply large n _ M hr hc
    simp; omega

end OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1
