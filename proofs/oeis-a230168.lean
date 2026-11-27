import OMAStatements.S_oeis_a230168
import Mathlib

/-!
# Proof of OEIS A230168 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a230168.main := by
  intro n hn
  cases n with
  | zero => exact (show ¬ (44 : ℕ).Prime by decide) hn |>.elim
  | succ k =>
    rw [pow_succ]
    have hpow : 0 < (2 : ℕ) ^ k := by positivity
    omega
