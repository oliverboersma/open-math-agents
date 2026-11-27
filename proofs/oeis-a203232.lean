import OMAStatements.S_oeis_a203232
import Mathlib

-- Problem: A203232, the recurrence and generating function of the elementary symmetric function
-- of degree n-1 of the repeating sequence 2, 3, 2, 3, ...
-- Upstream: formal-conjectures statements/oeis-a203232.lean (declaration OMA.S_oeis_a203232.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: two consecutive factors multiply to 6 and add to 5, so the pair (product, symmetric sum)
-- satisfies (p, e) -> (6p, 6e + 5p) every two steps; eliminating p gives the recurrence.

namespace OMA.P_oeis_a203232

open OMA.S_oeis_a203232

theorem digit_pair (n : ℕ) : digit n * digit (n + 1) = 6 ∧ digit n + digit (n + 1) = 5 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h' : (n + 1) % 2 = 1 := by omega
    simp only [digit, h, h']
    norm_num
  · have h' : (n + 1) % 2 = 0 := by omega
    simp only [digit, h, h']
    norm_num

theorem two_step (n : ℕ) :
    products (n + 2) = (6 * (products n).1, 6 * (products n).2 + 5 * (products n).1) := by
  obtain ⟨h1, h2⟩ := digit_pair n
  show (let (p, e) := products (n + 1); (p * digit (n + 1), e * digit (n + 1) + p)) = _
  rw [show products (n + 1) =
      (let (p, e) := products n; (p * digit n, e * digit n + p)) from rfl]
  obtain ⟨p, e⟩ := products n
  simp only [Prod.mk.injEq]
  constructor
  · rw [mul_assoc, h1, mul_comm]
  · linear_combination e * h1 + p * h2

theorem rec4 (k : ℕ) : a (k + 4) = 12 * a (k + 2) - 36 * a k := by
  have e2 := two_step (k + 2)
  have e0 := two_step k
  simp only [a]
  rw [e2, e0]
  simp only
  ring

theorem part1 : ∀ n : ℕ, 4 < n → a n = 12 * a (n - 2) - 36 * a (n - 4) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 2 = k + 2 by omega, show k + 4 - 4 = k by omega, rec4]

theorem a0 : a 0 = 0 := rfl
theorem a1 : a 1 = 1 := by decide
theorem a2 : a 2 = 5 := by decide
theorem a3 : a 3 = 16 := by decide

open PowerSeries in
theorem part2 : ((1 - C 6 * X^2 : ℤ⟦X⟧)^2 * mk a = X^1 + C 5 * X^2 + C 4 * X^3) := by
  have e : ((1 - C 6 * X^2 : ℤ⟦X⟧)^2) = 1 - C 12 * X ^ 2 + C 36 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [e]
  ext n
  rw [add_mul, sub_mul, one_mul, mul_assoc, mul_assoc, map_add, map_sub,
    coeff_C_mul, coeff_C_mul, mul_comm (X ^ 2), mul_comm (X ^ 4), coeff_mul_X_pow',
    coeff_mul_X_pow', coeff_mk, map_add, map_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    pow_one, coeff_X]
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> simp [a0, a1, a2, a3]
  · simp only [show 2 ≤ n by omega, show 4 ≤ n by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, ↓reduceIte, coeff_mk]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 2 = k + 2 by omega, show k + 4 - 4 = k by omega, rec4]
    ring

end OMA.P_oeis_a203232

theorem OMA.solution : type_of% @OMA.S_oeis_a203232.main :=
  ⟨OMA.P_oeis_a203232.part1, OMA.P_oeis_a203232.part2⟩
