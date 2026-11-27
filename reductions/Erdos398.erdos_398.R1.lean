import FormalConjectures.ErdosProblems.«398»
import Mathlib.Data.Nat.Sqrt

/-!
For n at least four, the square root in Brocard's equation is odd.
Writing it as 2x+1 reduces the problem to consecutive factors of n!/4.
-/

namespace OMA.R_Erdos398_erdos_398_R1

def H1 : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    ((∃ m : ℕ, n.factorial + 1 = m ^ 2) ↔
      ∃ x : ℕ, x * (x + 1) = n.factorial / 4)

def H2 : Prop :=
  ∀ n : ℕ, n < 128 →
    ((∃ m : ℕ, n.factorial + 1 = m ^ 2) ↔ n ∈ ({4, 5, 7} : Set ℕ))

def H3 : Prop :=
  ∀ n : ℕ, 128 ≤ n → ∀ x : ℕ, n.factorial / 4 ≠ x * (x + 1)

section Proof

theorem main : H1 → H2 → H3 → type_of% @Erdos398.erdos_398 := by
  intro factors initial tail
  ext n
  change (∃ m : ℕ, n.factorial + 1 = m ^ 2) ↔ n ∈ ({4, 5, 7} : Set ℕ)
  constructor
  · intro hn
    by_cases hsmall : n < 128
    · exact (initial n hsmall).mp hn
    obtain ⟨x, hx⟩ := (factors n (by omega)).mp hn
    exact (tail n (by omega) x hx.symm).elim
  · intro hn
    have hnsmall : n < 128 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with rfl | rfl | rfl <;> decide
    exact (initial n hnsmall).mpr hn

end Proof

end OMA.R_Erdos398_erdos_398_R1
