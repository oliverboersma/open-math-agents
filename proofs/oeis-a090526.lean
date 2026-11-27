import OMAStatements.S_oeis_a090526
import Mathlib

/-!
# Proof of OEIS A090526 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a090526.main := by
  intro n hn
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ n ^ n :=
    dvd_pow (Nat.minFac_dvd n) (by omega)
  obtain ⟨k, hk⟩ := hpd
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    simp at hk
  have hex : {j : ℕ | 1 ≤ j ∧ (n ^ n / j).Prime}.Nonempty := by
    refine ⟨k, Nat.succ_le_of_lt hkpos, ?_⟩
    rw [hk, Nat.mul_div_cancel p hkpos]
    exact hp
  have hmin : 1 ≤ OMA.S_oeis_a090526.a090525 n ∧
      (n ^ n / OMA.S_oeis_a090526.a090525 n).Prime := Nat.sInf_mem hex
  rw [OMA.S_oeis_a090526.a, if_neg (by omega : OMA.S_oeis_a090526.a090525 n ≠ 0)]
  exact hmin.2.ne_zero
