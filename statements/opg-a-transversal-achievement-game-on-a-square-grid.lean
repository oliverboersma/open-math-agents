import Mathlib

/-!
# The transversal achievement game

Source: Open Problem Garden, Transversal achievement game on a square grid.
Reference: Žarko Ranđelović, The transversal game, arXiv:2401.16768.

The first player tries to achieve a transversal before the second. A completed
board without a transversal for either side is a draw. The flag drawsAcceptable
distinguishes forcing a win from guaranteeing at least a draw.
-/

namespace OMA.S_opg_a_transversal_achievement_game_on_a_square_grid

abbrev Cell (n : ℕ) := Fin n × Fin n

def hasTransversal {n : ℕ} (claimed : List (Cell n)) : Bool :=
  (List.finRange n).all (fun row => claimed.any (fun cell => cell.1 = row)) &&
    decide (∃ placement : Equiv.Perm (Fin n),
      ∀ row : Fin n, (row, placement row) ∈ claimed)

def emptyCells (n : ℕ) : List (Cell n) :=
  (List.finRange n).flatMap (fun row => (List.finRange n).map (fun col => (row, col)))

def forceOutcome (drawsAcceptable : Bool) {n : ℕ} :
    List (Cell n) → Bool → List (Cell n) → List (Cell n) → ℕ → Bool
  | free, playerOneTurn, first, second, remaining =>
    if hasTransversal first then true
    else if hasTransversal second then false
    else if free.isEmpty then drawsAcceptable
    else match remaining with
      | 0 => drawsAcceptable
      | fuel + 1 =>
        if playerOneTurn then
          free.any (fun cell => forceOutcome drawsAcceptable (free.erase cell) false
            (cell :: first) second fuel)
        else
          free.all (fun cell => forceOutcome drawsAcceptable (free.erase cell) true
            first (cell :: second) fuel)

def firstWins (n : ℕ) : Bool := forceOutcome false (emptyCells n) true [] [] (n * n)

def firstAvoidsLoss (n : ℕ) : Bool := forceOutcome true (emptyCells n) true [] [] (n * n)

/-- The complete outcome of optimal play for every positive board size. -/
def ClaimedOutcome : Prop :=
  (∀ n : ℕ, 0 < n → n ≠ 2 → n ≠ 3 → firstWins n = true) ∧
    (firstWins 2 = false ∧ firstAvoidsLoss 2 = true) ∧
    (firstWins 3 = false ∧ firstAvoidsLoss 3 = true)

theorem main : ClaimedOutcome := by
  sorry

end OMA.S_opg_a_transversal_achievement_game_on_a_square_grid
