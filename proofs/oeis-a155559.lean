import OMAStatements.S_oeis_a155559
import Mathlib.Tactic

/-!
Repeated squaring shows that the exact power of two dividing
3^(2^(j+1)) - 1 is 2^(j+3). This determines the order of 3 modulo
each power of two from 8 onward, as recorded in OEIS A090129.
-/
-- Credit: @dk8827

namespace OMA.A155559

open OMA.S_oeis_a155559

private theorem square_step (j : ℕ) :
    ∃ u : ℕ, Odd u ∧ (3 : ℕ) ^ (2 ^ (j + 1)) = 1 + 2 ^ (j + 3) * u := by
  induction j with
  | zero => exact ⟨1, by decide, by decide⟩
  | succ j ih =>
    obtain ⟨u, hu, hpow⟩ := ih
    have heven : Even ((2 : ℕ) ^ (j + 2) * u) := even_iff_two_dvd.mpr
      (dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _)
    refine ⟨u * (1 + 2 ^ (j + 2) * u), hu.mul (odd_one.add_even heven), ?_⟩
    rw [show (2 : ℕ) ^ (j.succ + 1) = 2 ^ (j + 1) * 2 from pow_succ _ _,
      pow_mul, hpow,
      show (2 : ℕ) ^ (j.succ + 3) = 2 ^ (j + 2) * 2 ^ 2 by rw [← pow_add],
      show (2 : ℕ) ^ (j + 3) = 2 ^ (j + 2) * 2 from pow_succ _ _]
    ring

private theorem order_three (j : ℕ) :
    orderOf (3 : ZMod (2 ^ (j + 3))) = 2 ^ (j + 1) := by
  apply orderOf_eq_prime_pow (p := 2) (n := j)
  · cases j with
    | zero => decide
    | succ j =>
      intro h
      obtain ⟨u, hu, hpow⟩ := square_step j
      have hnat : (((3 : ℕ) ^ (2 ^ (j + 1)) : ℕ) : ZMod (2 ^ (j + 4))) = 1 := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
      rw [hpow, Nat.cast_add, Nat.cast_one] at hnat
      have hzero : ((2 ^ (j + 3) * u : ℕ) : ZMod (2 ^ (j + 4))) = 0 :=
        add_left_cancel (hnat.trans (add_zero 1).symm)
      have hd := (ZMod.natCast_eq_zero_iff (2 ^ (j + 3) * u) (2 ^ (j + 4))).mp hzero
      rw [show (2 : ℕ) ^ (j + 4) = 2 ^ (j + 3) * 2 from pow_succ _ _] at hd
      exact hu.not_two_dvd_nat (Nat.dvd_of_mul_dvd_mul_left (by positivity) hd)
  · obtain ⟨u, _, hpow⟩ := square_step j
    have hz : ((2 ^ (j + 3) * u : ℕ) : ZMod (2 ^ (j + 3))) = 0 :=
      (ZMod.natCast_eq_zero_iff (2 ^ (j + 3) * u) (2 ^ (j + 3))).mpr (dvd_mul_right _ _)
    have hnat : (((3 : ℕ) ^ (2 ^ (j + 1)) : ℕ) : ZMod (2 ^ (j + 3))) = 1 := by
      rw [hpow, Nat.cast_add, Nat.cast_one, hz, add_zero]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnat

theorem solution_aux (n : ℕ) : a n = A090129 (n + 3) - A090129 (n + 2) := by
  cases n with
  | zero =>
    have h4 : orderOf (3 : ZMod 4) = 2 := by apply orderOf_eq_prime <;> decide
    change 0 = orderOf (3 : ZMod (2 ^ (0 + 3))) - orderOf (3 : ZMod 4)
    norm_num [order_three 0, h4]
  | succ n =>
    simp only [a, A131577, Nat.succ_ne_zero, if_false, Nat.succ_sub_one, A090129]
    rw [order_three (n + 1), order_three n, pow_succ' (2 : ℕ) (n + 1), pow_succ' (2 : ℕ) n]
    omega

end OMA.A155559

theorem OMA.solution : type_of% @OMA.S_oeis_a155559.main := OMA.A155559.solution_aux
