import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Squarefree.Basic

/-!
# Equal means of parts and multiplicities in an integer partition

Source: https://oeis.org/A360070 (Gus Wiseman, OEIS Foundation, CC BY-SA 4.0).

Each part contributes once per occurrence to the mean of the parts. For the
other mean, each distinct part contributes its multiplicity once. A360070
asks whether every integer greater than 1 admitting such a partition has
a square factor greater than 1. A360068 counts these partitions.
-/

namespace OMA.S_oeis_a360070

def SameMeans {n : ℕ} (P : n.Partition) : Prop :=
  (P.parts.sum : ℚ) / P.parts.card =
    ((∑ a ∈ P.parts.toFinset, P.parts.count a : ℕ) : ℚ) / P.parts.toFinset.card

theorem main : ∀ n : ℕ, 1 < n → (∃ P : n.Partition, SameMeans P) → ¬ Squarefree n := by
  sorry

end OMA.S_oeis_a360070
