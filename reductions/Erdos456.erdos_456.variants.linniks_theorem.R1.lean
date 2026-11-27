import FormalConjectures.ErdosProblems.«456»
import Mathlib

/-! The polynomial bound for the least prime p_n that is 1 mod n, from Linnik's theorem on the
least prime in an arithmetic progression (Linnik, On the least prime in an arithmetic
progression, Mat. Sbornik 15 (1944)). Linnik's theorem is stated here for the residue class 1
in the same form as the hypothesis H2 of the merged reduction
Erdos694.erdos_694.R1, so one proof serves both. The remaining step is the passage from the
existence of a small prime to a bound for the infimum p_n. -/

namespace OMA.R_Erdos456_erdos_456_variants_linniks_theorem_R1
open Filter Asymptotics

/-- Linnik's theorem for the residue class 1. -/
def H1 : Prop := ∃ C : ℝ, ∃ L : ℕ, 1 ≤ C ∧ 1 ≤ L ∧
  ∀ M : ℕ, 1 ≤ M → ∃ ℓ : ℕ, Nat.Prime ℓ ∧ M ∣ ℓ - 1 ∧ (ℓ : ℝ) ≤ C * (M : ℝ) ^ L

/-- A prime that is 1 mod n and at most C n^L for every n bounds the least such prime. -/
def H2 : Prop := ∀ (C : ℝ) (L : ℕ),
  (∀ M : ℕ, 1 ≤ M → ∃ ℓ : ℕ, Nat.Prime ℓ ∧ M ∣ ℓ - 1 ∧ (ℓ : ℝ) ≤ C * (M : ℝ) ^ L) →
  (fun n : ℕ ↦ (Erdos456.p n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (L : ℝ))

theorem main : H1 → H2 → type_of% @Erdos456.erdos_456.variants.linniks_theorem := by
  rintro ⟨C, L, _, _, h⟩ h2
  exact ⟨(L : ℝ), h2 C L h⟩

end OMA.R_Erdos456_erdos_456_variants_linniks_theorem_R1
