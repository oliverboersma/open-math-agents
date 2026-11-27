import OMAStatements.S_oeis_a131418
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a131418.main := by
  intro n h
  unfold OMA.S_oeis_a131418.IsTerm OMA.S_oeis_a131418.digitSum at h
  have h1 : n ≡ (Nat.digits 10 n).sum [MOD 9] := Nat.modEq_nine_digits_sum n
  have h2 : n + (Nat.digits 10 n).sum ≡
      (Nat.digits 10 (n + (Nat.digits 10 n).sum)).sum [MOD 9] :=
    Nat.modEq_nine_digits_sum _
  rw [← h] at h2
  unfold Nat.ModEq at h1 h2
  omega
