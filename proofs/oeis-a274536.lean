import OMAStatements.S_oeis_a274536
import Mathlib.Tactic

/-!
The factor of the divisor sum coming from primes other than 5 cancels.
The geometric sum at 5 increases by a factor of six precisely when the
initial power of 5 is zero.
-/
-- Credit: @dk8827

namespace OMA.A274536

open ArithmeticFunction

private theorem sigma_five_succ (e : ℕ) :
    sigma 1 ((5 : ℕ) ^ (e + 1)) = 1 + 5 * sigma 1 ((5 : ℕ) ^ e) := by
  have hp : Nat.Prime 5 := by decide
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
    Finset.mul_sum]
  simp [pow_succ', Nat.add_comm]

theorem solution_aux (n : ℕ) (hn : 0 < n) :
    OMA.S_oeis_a274536.a n = sigma 1 (5 * n) ↔ ¬ 5 ∣ n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 5 (by decide)
  have hp : Nat.Prime 5 := by decide
  have hs (j : ℕ) : sigma 1 (5 ^ j * m) = sigma 1 (5 ^ j) * sigma 1 m :=
    isMultiplicative_sigma.map_mul_of_coprime ((hp.coprime_iff_not_dvd.mpr hm).pow_left j)
  have hsm : 0 < sigma 1 m := sigma_pos 1 m (by
    intro h
    simp [h] at hn)
  have heq : 5 * (5 ^ e * m) = 5 ^ (e + 1) * m := by rw [pow_succ', mul_assoc]
  rw [OMA.S_oeis_a274536.a, heq, hs, hs, sigma_five_succ, ← mul_assoc]
  cases e with
  | zero => simp [hm]
  | succ j =>
    have hd : 5 ∣ 5 ^ (j + 1) * m := dvd_mul_of_dvd_left (dvd_pow_self 5 (by omega)) m
    simp only [hd, not_true_eq_false, iff_false]
    intro h
    have hcancel := Nat.eq_of_mul_eq_mul_right hsm h
    rw [sigma_five_succ] at hcancel
    have hpos := sigma_pos 1 ((5 : ℕ) ^ j) (pow_ne_zero _ (by decide))
    omega

end OMA.A274536

theorem OMA.solution : type_of% @OMA.S_oeis_a274536.main := OMA.A274536.solution_aux
