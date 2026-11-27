import OMAStatements.S_oeis_a130729
import Mathlib

/-!
# Proof of OEIS A130729 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a130729.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hn
  have h₃ : 2 ^ (2 * k + 1) ≡ 2 [MOD 3] := by
    have h : 4 ≡ 1 [MOD 3] := by decide
    rw [pow_succ, pow_mul]
    change 4 ^ k * 2 ≡ 2 [MOD 3]
    simpa only [one_pow, one_mul] using (h.pow k).mul_right 2
  change 2 ^ (2 * k + 1) % 3 = 2 at h₃
  let m := 2 ^ (2 * k + 1) / 3
  have hexp : 2 ^ (2 * k + 1) = 3 * m + 2 := by
    dsimp [m]
    omega
  have h₇ : 8 ≡ 1 [MOD 7] := by decide
  apply Nat.modEq_zero_iff_dvd.mp
  calc
    OMA.S_oeis_a130729.a (2 * k + 1) = 8 ^ m * 4 + 3 := by
      unfold OMA.S_oeis_a130729.a
      rw [hexp, pow_add, pow_mul]
      rfl
    _ ≡ 7 [MOD 7] := by
      simpa only [one_pow, one_mul] using ((h₇.pow m).mul_right 4).add_right 3
    _ ≡ 0 [MOD 7] := by decide
