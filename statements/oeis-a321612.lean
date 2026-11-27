import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Fin

/-!
# Triangular sums reflected across the midpoint

Source: https://oeis.org/A321612 (Frank M Jackson, OEIS Foundation, CC BY-SA 4.0).

For each k the entry takes all triangular numbers t with k/2 ≤ t < k,
requires this collection to be nonempty, and asks whether every k-t is
also triangular. It conjectures that exactly the nine listed values qualify.
-/

namespace OMA.S_oeis_a321612

def tri (i : ℕ) : ℕ := i*(i+1)/2

def triangular (v : ℕ) : Prop :=
  ∃ i : Fin (v+1), tri i.val = v

def inTerms (k : ℕ) : Prop :=
  (∃ t : Fin k, k ≤ 2*t.val ∧ triangular t.val) ∧
    ∀ t : Fin k, k ≤ 2*t.val → triangular t.val → triangular (k-t.val)

theorem main : {k : ℕ | inTerms k} = {2, 4, 6, 7, 9, 13, 16, 21, 31} := by
  sorry

end OMA.S_oeis_a321612
