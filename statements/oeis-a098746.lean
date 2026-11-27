import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Monotone.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Burstein's permutation-avoidance conjecture in OEIS A098746

Source: https://oeis.org/A098746 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

An occurrence is a subsequence of the permutation whose entries have the
same relative order as the listed pattern. The count includes the empty
permutation at the start of the sequence.
-/

namespace OMA.S_oeis_a098746

def Avoids {n k : ℕ} (σ : Equiv.Perm (Fin n)) (pattern : Fin k → ℕ) : Prop :=
  ¬ ∃ positions : Fin k → Fin n, StrictMono positions ∧
    ∀ i j, σ (positions i) < σ (positions j) ↔ pattern i < pattern j

theorem main : ∀ n : ℕ,
    Nat.card {σ : Equiv.Perm (Fin n) // Avoids σ ![4, 2, 3, 1] ∧ Avoids σ ![4, 2, 5, 1, 3]} =
    Nat.card {σ : Equiv.Perm (Fin n) // Avoids σ ![1, 3, 4, 2] ∧ Avoids σ ![1, 3, 2, 5, 4]} := by
  sorry

end OMA.S_oeis_a098746
