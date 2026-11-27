import OMAStatements.S_oeis_a213382
import Mathlib

namespace OMAa213382

theorem modk (k : ℕ) (hk : k.Prime) (h5 : 5 ≤ k) :
    (3 * k - 2) ^ (3 * k - 2) ≡ 3 * k - 2 [MOD k] := by
  haveI := Fact.mk hk
  rw [← ZMod.natCast_eq_natCast_iff]
  have hne : ((3 * k - 2 : ℕ) : ZMod k) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have h2 : k ∣ 3 * k - (3 * k - 2) := Nat.dvd_sub (dvd_mul_left k 3) h
    rw [show 3 * k - (3 * k - 2) = 2 by omega] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have he : 3 * k - 2 = (k - 1) * 3 + 1 := by omega
  rw [Nat.cast_pow]
  calc ((3 * k - 2 : ℕ) : ZMod k) ^ (3 * k - 2)
      = ((3 * k - 2 : ℕ) : ZMod k) ^ ((k - 1) * 3 + 1) := by rw [← he]
    _ = ((3 * k - 2 : ℕ) : ZMod k) := by
      rw [pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one hne, one_pow, one_mul]

theorem mod3 (k : ℕ) (h5 : 5 ≤ k) :
    (3 * k - 2) ^ (3 * k - 2) ≡ 3 * k - 2 [MOD 3] := by
  have h1 : 3 * k - 2 ≡ 1 [MOD 3] := by
    unfold Nat.ModEq; omega
  calc (3 * k - 2) ^ (3 * k - 2) ≡ 1 ^ (3 * k - 2) [MOD 3] := h1.pow _
    _ = 1 := one_pow _
    _ ≡ 3 * k - 2 [MOD 3] := h1.symm

end OMAa213382

theorem OMA.solution : type_of% @OMA.S_oeis_a213382.main := by
  intro k hk
  rcases hk with rfl | hk
  · norm_num
  · by_cases h2 : k = 2
    · subst h2; norm_num
    by_cases h3 : k = 3
    · subst h3; norm_num
    have h5 : 5 ≤ k := by
      have := hk.two_le
      by_contra hc
      have h4 : k = 4 := by omega
      subst h4; norm_num at hk
    have hcop : Nat.Coprime 3 k :=
      (Nat.coprime_primes Nat.prime_three hk).mpr (by omega)
    have hm := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
      ⟨OMAa213382.mod3 k h5, OMAa213382.modk k hk h5⟩
    rw [hm]
    exact Nat.mod_eq_of_lt (by omega)
