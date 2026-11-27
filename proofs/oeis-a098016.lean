import OMAStatements.S_oeis_a098016
import Mathlib

/-!
# Proof of OEIS A098016 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a098016.main := by
  rintro x ⟨q, hq, hsum⟩
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hp : Nat.nth Nat.Prime x < Nat.nth Nat.Prime (x + 1) :=
    hmono (Nat.lt_succ_self x)
  have hlo : Nat.nth Nat.Prime x < q := by omega
  have hhi : q < Nat.nth Nat.Prime (x + 1) := by omega
  rw [← Nat.nth_count hq] at hlo hhi
  have hlo' := hmono.lt_iff_lt.mp hlo
  have hhi' := hmono.lt_iff_lt.mp hhi
  omega
