import OMAStatements.S_oeis_a129527
import Mathlib

/-!
# Proof of OEIS A129527 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a129527.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases he : n % 2 = 0
    · have hstep : OMA.S_oeis_a129527.a n = OMA.S_oeis_a129527.a (n / 2) + n := by
        cases n with
        | zero => omega
        | succ k => rw [OMA.S_oeis_a129527.a, if_pos he]
      have hpart : OMA.S_oeis_a129527.oddPart (n / 2) = OMA.S_oeis_a129527.oddPart n :=
        Nat.ordCompl_div_of_dvd Nat.prime_two (Nat.dvd_of_mod_eq_zero he)
      have hle : OMA.S_oeis_a129527.oddPart (n / 2) ≤ n / 2 := Nat.ordCompl_le (n / 2) 2
      rw [hstep, ih (n / 2) (by omega) (by omega), ← hpart]
      omega
    · have hstep : OMA.S_oeis_a129527.a n = n := by
        cases n with
        | zero => omega
        | succ k => rw [OMA.S_oeis_a129527.a, if_neg he]
      have hndvd : ¬ 2 ∣ n := fun hd => he (Nat.mod_eq_zero_of_dvd hd)
      have hpart : OMA.S_oeis_a129527.oddPart n = n := by
        simp [OMA.S_oeis_a129527.oddPart, Nat.factorization_eq_zero_of_not_dvd hndvd]
      rw [hstep, hpart]
      omega
