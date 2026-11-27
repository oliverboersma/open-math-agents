import OMAStatements.S_oeis_a396111
import Mathlib

/-!
# Proof of OEIS A396111 conjecture

Credit: @AkiRA-COM-FP
-/

namespace OMA.P_oeis_a396111

private theorem mul_a_modEq_one (n : ℕ) :
    16 * OMA.S_oeis_a396111.a n ≡ 1 [MOD 2 * n + 1] := by
  have hzero : 2 * n + 1 ≡ 0 [MOD 2 * n + 1] :=
    Nat.modEq_zero_iff_dvd.mpr dvd_rfl
  have hsquare : (2 * n) ^ 2 ≡ 1 [MOD 2 * n + 1] := by
    apply Nat.ModEq.add_right_cancel' (2 * n)
    have hmul := hzero.mul_right (2 * n)
    rw [add_mul, one_mul, ← pow_two, zero_mul] at hmul
    exact hmul.trans (by simpa only [add_comm 1 (2 * n)] using hzero.symm)
  calc
    16 * OMA.S_oeis_a396111.a n ≡ 16 * n ^ 4 [MOD 2 * n + 1] :=
      (Nat.mod_modEq _ _).mul_left 16
    _ = (2 * n) ^ 4 := by ring
    _ ≡ 1 [MOD 2 * n + 1] := by simpa only [← pow_mul, one_pow] using hsquare.pow 2

end OMA.P_oeis_a396111

theorem OMA.solution : type_of% @OMA.S_oeis_a396111.main := by
  constructor
  · intro k
    by_cases hk : k = 0
    · exact ⟨0, hk.symm⟩
    let n := 8 * k - 1
    refine ⟨n, ?_⟩
    have hm : 2 * n + 1 = 16 * k - 1 := by
      dsimp [n]
      omega
    have hkmod : 16 * k ≡ 1 [MOD 2 * n + 1] := by
      rw [hm]
      exact Nat.modEq_sub (by omega)
    have hc := (Nat.coprime_of_mul_modEq_one k hkmod).symm
    have hmod := Nat.ModEq.cancel_left_of_coprime hc
      ((OMA.P_oeis_a396111.mul_a_modEq_one n).trans hkmod.symm)
    exact hmod.eq_of_lt_of_lt (Nat.mod_lt _ (by omega)) (by omega)
  · intro k
    refine (Set.finite_Iic (8 * k)).subset ?_
    intro n hn
    change OMA.S_oeis_a396111.a n = k at hn
    change n ≤ 8 * k
    have h := OMA.P_oeis_a396111.mul_a_modEq_one n
    rw [hn] at h
    by_cases hk : k = 0
    · rw [hk, mul_zero] at h
      have hdiv : 2 * n + 1 ∣ 1 := Nat.modEq_zero_iff_dvd.mp h.symm
      have hbound := Nat.le_of_dvd (by decide : 0 < (1 : ℕ)) hdiv
      omega
    · have hdiv : 2 * n + 1 ∣ 16 * k - 1 := h.symm.dvd'
      have hbound := Nat.le_of_dvd (by omega) hdiv
      omega
