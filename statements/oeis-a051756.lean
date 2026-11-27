import Mathlib

/-!
# Queens attacking precisely three other queens

Source: https://oeis.org/A051756 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @physbuzz.

On each line through a queen, the nearest occupied square on either side
is the only visible queen on that side. Row-major order is monotone along
each line, so it distinguishes these two sides even on a descending diagonal.
-/

namespace OMA.S_oeis_a051756

abbrev Square (n : ℕ) := Fin n × Fin n

inductive Axis | row | column | ascending | descending
  deriving DecidableEq

def line {n : ℕ} (a : Axis) (p : Square n) : ℕ :=
  match a with
  | .row => p.1.val
  | .column => p.2.val
  | .ascending => p.1.val + p.2.val
  | .descending => p.1.val + (n - 1 - p.2.val)

def rank {n : ℕ} (p : Square n) := p.1.val * n + p.2.val

def visible {n : ℕ} (s : Finset (Square n)) (p : Square n) (a : Axis) : ℕ :=
  (if ∃ q ∈ s, line a q = line a p ∧ rank q < rank p then 1 else 0) +
  (if ∃ q ∈ s, line a q = line a p ∧ rank p < rank q then 1 else 0)

def valid {n : ℕ} (s : Finset (Square n)) : Prop :=
  ∀ p ∈ s, visible s p .row + visible s p .column +
    visible s p .ascending + visible s p .descending = 3

/-- Alexander D. Healy's formula for the maximum size of a valid placement. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    IsGreatest {k : ℕ | ∃ s : Finset (Square n), valid s ∧ s.card = k}
      (2 * ((6 * n - 2) / 5)) := by
  sorry

end OMA.S_oeis_a051756
