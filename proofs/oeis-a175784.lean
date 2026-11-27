import OMAStatements.S_oeis_a175784
import Mathlib

-- Problem: A175784, the reduced numerators of (2n-1)/(2n+9) + 1.
-- Upstream: formal-conjectures statements/oeis-a175784.lean (declaration OMA.S_oeis_a175784.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: (2n-1)/(2n+9) + 1 = 4(n+2)/(2n+9) and gcd(4(n+2), 2n+9) = gcd(n+2, 5), so the numerator
-- is 4(n+2)/gcd(n+2, 5); the recurrence and generating function follow from 5-periodicity.

namespace OMA.P_oeis_a175784

open OMA.S_oeis_a175784

theorem q_eq (n : ℕ) : q n = (((4 * (n + 2) : ℕ) : ℤ) : ℚ) / (((2 * n + 9 : ℕ) : ℤ) : ℚ) := by
  unfold q
  push_cast
  field_simp
  ring

theorem num_of_coprime (u v : ℕ) (hv : 0 < v) (h : Nat.Coprime u v) :
    ((((u : ℕ) : ℤ) : ℚ) / (((v : ℕ) : ℤ) : ℚ)).num = u := by
  apply Rat.num_div_eq_of_coprime
  · exact_mod_cast hv
  · simpa using h

theorem coprime5 (m : ℕ) (h : ¬ m % 5 = 0) : Nat.Coprime 5 m :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr (fun hd => h (Nat.mod_eq_zero_of_dvd hd))

theorem gcd5 (m : ℕ) : Nat.gcd m 5 = if m % 5 = 0 then 5 else 1 := by
  split_ifs with h
  · exact Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h)
  · exact Nat.Coprime.gcd_eq_one (coprime5 m h).symm

theorem coprime4 (m : ℕ) (h : m % 2 = 1) : Nat.Coprime (2 ^ 2) m := by
  apply Nat.Coprime.pow_left 2
  rw [Nat.coprime_two_left]
  exact Nat.odd_iff.mpr h

theorem part1 (n : ℕ) : a n = 4 * (((n + 2) / Nat.gcd (n + 2) 5 : ℕ) : ℤ) := by
  unfold a
  rw [gcd5]
  split_ifs with h
  · obtain ⟨k, hk⟩ : ∃ k, n + 2 = 5 * k := ⟨(n + 2) / 5, by omega⟩
    have hq : q n = (((4 * k : ℕ) : ℤ) : ℚ) / (((2 * k + 1 : ℕ) : ℤ) : ℚ) := by
      rw [q_eq]
      rw [div_eq_div_iff (by positivity) (by positivity)]
      push_cast
      have : (n : ℚ) + 2 = 5 * k := by exact_mod_cast hk
      linear_combination 4 * this
    rw [hq, num_of_coprime _ _ (by omega)]
    · rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
      push_cast
      ring
    · rw [Nat.coprime_mul_iff_left]
      refine ⟨by simpa using coprime4 (2 * k + 1) (by omega), ?_⟩
      rw [Nat.coprime_comm, show 2 * k + 1 = 1 + 2 * k by ring, Nat.coprime_add_mul_right_left]
      exact Nat.coprime_one_left k
  · rw [q_eq, num_of_coprime _ _ (by omega)]
    · push_cast
      simp
    · rw [Nat.coprime_mul_iff_left]
      refine ⟨by simpa using coprime4 (2 * n + 9) (by omega), ?_⟩
      rw [show 2 * n + 9 = 5 + 2 * (n + 2) by ring, Nat.coprime_comm,
        Nat.coprime_add_mul_right_left]
      exact coprime5 (n + 2) h

theorem part2 (n : ℕ) (hn : 11 ≤ n) : a n = 2 * a (n - 5) - a (n - 10) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
  rw [part1, part1, part1, show k + 10 - 5 = k + 5 by omega, show k + 10 - 10 = k by omega,
    gcd5, gcd5, gcd5]
  have e1 : (k + 5 + 2) % 5 = (k + 2) % 5 := by omega
  have e2 : (k + 10 + 2) % 5 = (k + 2) % 5 := by omega
  rw [e1, e2]
  split_ifs <;> push_cast <;> omega

theorem a_val (n : ℕ) : a n = 4 * (((n + 2) / (if (n + 2) % 5 = 0 then 5 else 1) : ℕ) : ℤ) := by
  rw [part1, gcd5]

open PowerSeries in
theorem part3 : series * ((X - 1)^2 * (X^4 + X^3 + X^2 + X + 1)^2) =
      -4 * X * (-3 - 4*X - X^2 - 6*X^3 - 7*X^4 - 2*X^5 - X^6 + X^8 + 2*X^9) := by
  have hden : ((X - 1)^2 * (X^4 + X^3 + X^2 + X + 1)^2 : PowerSeries ℚ) =
      1 - C (2 : ℚ) * X ^ 5 + X ^ 10 := by
    simp only [map_ofNat]
    ring
  have hnum : (-4 * X * (-3 - 4*X - X^2 - 6*X^3 - 7*X^4 - 2*X^5 - X^6 + X^8 + 2*X^9) :
      PowerSeries ℚ) =
      C (12 : ℚ) * X ^ 1 + C (16 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3 + C (24 : ℚ) * X ^ 4 +
      C (28 : ℚ) * X ^ 5 + C (8 : ℚ) * X ^ 6 + C (4 : ℚ) * X ^ 7 + C (-4 : ℚ) * X ^ 9 +
      C (-8 : ℚ) * X ^ 10 := by
    simp only [map_neg, map_ofNat]
    ring
  rw [hden, hnum]
  ext n
  rw [mul_add, mul_sub, mul_one, mul_comm (C (2 : ℚ)) (X ^ 5), ← mul_assoc, map_add, map_sub,
    coeff_mul_C, coeff_mul_X_pow', coeff_mul_X_pow']
  simp only [map_add, coeff_C_mul_X_pow, series, coeff_mk]
  rcases Nat.lt_or_ge n 11 with h | h
  · interval_cases n <;> norm_num [a_val]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
    simp only [show 5 ≤ k + 11 by omega, show 10 ≤ k + 11 by omega, show k + 11 ≠ 0 by omega,
      show k + 11 - 5 ≠ 0 by omega, show k + 11 - 10 ≠ 0 by omega, show k + 11 ≠ 1 by omega,
      show k + 11 ≠ 2 by omega, show k + 11 ≠ 3 by omega, show k + 11 ≠ 4 by omega,
      show k + 11 ≠ 5 by omega, show k + 11 ≠ 6 by omega, show k + 11 ≠ 7 by omega,
      show k + 11 ≠ 9 by omega, show k + 11 ≠ 10 by omega, ↓reduceIte]
    rw [part2 (k + 11) (by omega)]
    push_cast
    ring


end OMA.P_oeis_a175784

theorem OMA.solution : type_of% @OMA.S_oeis_a175784.main :=
  ⟨fun n _ => OMA.P_oeis_a175784.part1 n, OMA.P_oeis_a175784.part2, OMA.P_oeis_a175784.part3⟩
