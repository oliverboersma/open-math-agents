import OMAStatements.S_oeis_a087038
import Mathlib

open OMA.S_oeis_a087038

private theorem not_prime_add_125 {x : ℕ} (hx : 0 < x) : ¬ (x ^ x + 125).Prime := by
  by_cases heven : x % 2 = 0
  · by_cases hthree : x % 3 = 0
    · let u := x ^ (x / 3)
      have hpow : x ^ x = u ^ 3 := by
        change x ^ x = (x ^ (x / 3)) ^ 3
        rw [← pow_mul]
        exact congrArg (fun e : ℕ => x ^ e) (by omega)
      have hxu : x ≤ u := Nat.le_pow (by omega)
      have hu : 5 ≤ u := by omega
      obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hu
      have hfactor : u ^ 3 + 125 = (u + 5) * (v ^ 2 + 5 * v + 25) := by
        rw [hv]
        ring
      rw [hpow, hfactor]
      exact Nat.not_prime_mul (by omega) (by omega)
    · have hsq : x ^ 2 ≡ 1 [MOD 3] := by
        change x ^ 2 % 3 = 1 % 3
        rw [Nat.pow_mod]
        have hres : x % 3 = 1 ∨ x % 3 = 2 := by omega
        rcases hres with h | h <;> rw [h]
      have hpow : x ^ x = (x ^ 2) ^ (x / 2) := by
        rw [← pow_mul]
        exact congrArg (fun e : ℕ => x ^ e) (by omega)
      have hmod : x ^ x + 125 ≡ 0 [MOD 3] := calc
        x ^ x + 125 ≡ 1 ^ (x / 2) + 125 [MOD 3] := by
          rw [hpow]
          exact (hsq.pow (x / 2)).add_right 125
        _ ≡ 0 [MOD 3] := by rw [one_pow]; decide
      exact Nat.not_prime_of_dvd_of_lt (Nat.modEq_zero_iff_dvd.mp hmod) (by decide) (by omega)
  · have hodd : x ≡ 1 [MOD 2] := by
      change x % 2 = 1 % 2
      omega
    have hmod : x ^ x + 125 ≡ 0 [MOD 2] := calc
      x ^ x + 125 ≡ 1 ^ x + 125 [MOD 2] := (hodd.pow x).add_right 125
      _ ≡ 0 [MOD 2] := by rw [one_pow]; decide
    exact Nat.not_prime_of_dvd_of_lt (Nat.modEq_zero_iff_dvd.mp hmod) (by decide) (by omega)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a087038.main) := by
  intro h
  obtain ⟨x, hx, hp⟩ := h 125 (by decide)
  exact not_prime_add_125 (by omega) hp
