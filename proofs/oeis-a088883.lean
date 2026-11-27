import OMAStatements.S_oeis_a088883
import Mathlib

open OMA.S_oeis_a088883

lemma OMA.rev3 (p : ℕ) : rev p % 3 = p % 3 := by
  have h1 : rev p ≡ Nat.ofDigits (10 % 3) (Nat.digits 10 p).reverse [MOD 3] := Nat.ofDigits_modEq 10 3 _
  have h2 : p ≡ (Nat.digits 10 p).sum [MOD 3] := Nat.modEq_three_digits_sum p
  rw [show 10 % 3 = 1 by norm_num, Nat.ofDigits_one, List.sum_reverse] at h1
  exact h1.trans h2.symm

theorem OMA.solution : type_of% @OMA.S_oeis_a088883.main := by
  intro p hp hN
  set L := (Nat.digits 10 p).length
  set N := p * 10 ^ L + rev p + 2 with hNdef
  have hr := OMA.rev3 p
  have h10 : 10 ^ L % 3 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have hN3 : N % 3 = (2 * p + 2) % 3 := by
    rw [hNdef, Nat.add_mod, Nat.add_mod (p * 10 ^ L), Nat.mul_mod, h10, hr]; omega
  have hNbig : 3 < N := by
    have : 1 ≤ 10 ^ L := Nat.one_le_pow _ _ (by norm_num)
    have := hp.two_le
    rw [hNdef]; nlinarith
  have h3 : p % 3 = 1 := by
    rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h
    · have : p = 3 := ((Nat.Prime.eq_one_or_self_of_dvd hp 3 (by omega)).resolve_left (by norm_num)).symm
      subst this
      exfalso; revert hN; decide
    · exact h
    · exfalso
      have : 3 ∣ N := by omega
      have := (Nat.Prime.eq_one_or_self_of_dvd hN 3 this)
      omega
  have h2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · subst h; exfalso; revert hN; decide
    · exact h
  omega
