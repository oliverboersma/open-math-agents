import Mathlib

/-!
# The maximum total number of queen moves on a square chessboard

Source: https://oeis.org/A275815 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @physbuzz.

The queens all belong to the same side. For each empty destination and each
of its eight rays, there is one legal move from that ray if it contains an
occupied square. The nearest queen can move there, and it blocks every queen
farther away. This counts directed source-to-destination moves once each.
-/

namespace OMA.S_oeis_a275815

abbrev Square (n : ℕ) := Fin n × Fin n

def rays : Finset (ℤ × ℤ) :=
  {(-1,-1), (-1,0), (-1,1), (0,-1), (0,1), (1,-1), (1,0), (1,1)}

def canArrive {n : ℕ} (s : Finset (Square n)) (p : Square n) (v : ℤ × ℤ) : Prop :=
  p ∉ s ∧ ∃ q ∈ s, ∃ k ∈ Finset.Ico 1 n,
    (q.1.val : ℤ) = p.1.val + k*v.1 ∧ (q.2.val : ℤ) = p.2.val + k*v.2

noncomputable def moves {n : ℕ} (s : Finset (Square n)) : ℕ := by
  classical
  exact ∑ p : Square n, (rays.filter (canArrive s p)).card

/-- Alec Jones's conjecture for every board side of at least six. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    IsGreatest {m : ℕ | ∃ s : Finset (Square n), moves s = m} (8*(n-2)^2) := by
  sorry

end OMA.S_oeis_a275815
