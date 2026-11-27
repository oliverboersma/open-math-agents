import OMAStatements.S_oeis_a191993
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

open OMA.S_oeis_a191993

theorem OMA.solution : type_of% @OMA.S_oeis_a191993.main := by
  have step (j : ℕ) : ((j : ℚ) + 1) * (Nat.centralBinom (j + 1) : ℚ) =
      2 * (2 * (j : ℚ) + 1) * (Nat.centralBinom j : ℚ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ j
  intro t
  have h1 := step (t + 1)
  have h2 := step (t + 2)
  push_cast at h1 h2
  simp [a, pow_add]
  linear_combination (t : ℚ) / 2 * h2 - 3 / 2 * ((t : ℚ) + 1) * h1
