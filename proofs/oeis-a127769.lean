import OMAStatements.S_oeis_a127769
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open OMA.S_oeis_a127769

theorem OMA.solution : type_of% @OMA.S_oeis_a127769.main := by
  intro t
  dsimp only [term]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  field_simp
  ring
