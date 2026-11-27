import OMAStatements.S_oeis_a257379
import Mathlib

/-!
# Proof of OEIS A257379 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a257379.main := by
  intro n hn
  let t : ℕ := n * 2 ^ n
  have ht : 0 < t := Nat.mul_pos hn (by positivity)
  have heven : 2 ∣ t :=
    dvd_mul_of_dvd_right (by simpa using (pow_dvd_pow 2 hn : 2 ^ 1 ∣ 2 ^ n)) n
  have ht₂ : 2 ≤ t := Nat.le_of_dvd ht heven
  have hc₂ : (t - 1).Coprime 2 := by
    have hmod : t % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp heven
    exact Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by omega))
  have hct : (t - 1).Coprime t := (Nat.coprime_self_sub_left ht).mpr (Nat.coprime_one_left t)
  obtain ⟨p, hpt, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (t - 1) (q := 2 * t) (a := t - 1)
      (by positivity) (hc₂.mul_right hct)
  obtain ⟨m, hm⟩ := hmod.symm.dvd'
  have heq : (2 * m + 1) * t = p + 1 := by
    calc
      (2 * m + 1) * t = (2 * t) * m + t := by ring
      _ = p + 1 := by omega
  refine ⟨2 * m + 1, odd_iff_exists_bit1.mpr ⟨m, rfl⟩, ?_⟩
  rw [mul_assoc]
  change ((2 * m + 1) * t - 1).Prime
  rwa [heq, Nat.add_sub_cancel]
