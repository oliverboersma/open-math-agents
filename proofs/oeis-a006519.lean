import OMAStatements.S_oeis_a006519
import Mathlib

open ArithmeticFunction

namespace DivisorSumDoubling

lemma sigma_two_pow (k : ℕ) : (sigma 1 (2 ^ k) : ℚ) = 2 * (2 : ℚ)^k - 1 := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  push_cast
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

end DivisorSumDoubling

theorem OMA.solution : type_of% @OMA.S_oeis_a006519.main := by
  intro n hn
  let k := n.factorization 2
  let m := ordCompl[2] n
  have hm : 2 ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hc : Nat.Coprime 2 m := Nat.coprime_ordCompl Nat.prime_two (by omega)
  have hs (j : ℕ) :
      (sigma 1 (2 ^ j * m) : ℚ) = (2 * (2 : ℚ)^j - 1) * (sigma 1 m : ℚ) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left j)]
    push_cast
    rw [DivisorSumDoubling.sigma_two_pow]
  have hmpos : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, mul_zero] at hm
    omega
  have hsig : 0 < (sigma 1 m : ℚ) := by exact_mod_cast (sigma_pos_iff.mpr hmpos : 0 < sigma 1 m)
  have hpow : 1 ≤ (2 : ℚ) ^ k := one_le_pow₀ (by norm_num)
  have hden : 2 * (2 : ℚ)^k - 1 ≠ 0 := by linarith
  have hd : 2 * n = 2^(k+1) * m := by rw [← hm, pow_succ']; ring
  change (↑(2^k : ℕ) : ℚ) = _
  push_cast
  rw [hd, hs, ← hm, hs, pow_succ]
  have hratio :
      ((2 * ((2 : ℚ)^k * 2) - 1) * (sigma 1 m : ℚ)) /
        ((2 * (2 : ℚ)^k - 1) * (sigma 1 m : ℚ)) - 2 =
        1 / (2 * (2 : ℚ)^k - 1) := by
    field_simp [hden, hsig.ne']
    ring
  rw [hratio, one_div_one_div]
  ring
