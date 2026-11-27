import OMAStatements.S_oeis_a203165
import Mathlib

/-!
# A203165: recurrence and generating function

Over any four consecutive indices the digits are a rotation of 3, 4, 1, 2, whose product is 24 and
whose third elementary symmetric function is 50. Hence (P, E) = products n satisfies
P(n+4) = 24 P(n) and E(n+4) = 24 E(n) + 50 P(n), and eliminating P gives
E(n+8) = 48 E(n+4) − 576 E(n) for every n. The generating-function identity follows by comparing
coefficients: the first eight are computed directly and the rest vanish by the recurrence.
-/

namespace A203165Proof
open OMA.S_oeis_a203165

theorem step (n : ℕ) :
    products (n + 1) = ((products n).1 * digit n, (products n).2 * digit n + (products n).1) := by
  rw [products]

theorem digit_prod (n : ℕ) :
    digit n * digit (n + 1) * digit (n + 2) * digit (n + 3) = 24 ∧
    digit (n + 1) * digit (n + 2) * digit (n + 3) + digit n * digit (n + 2) * digit (n + 3) +
      digit n * digit (n + 1) * digit (n + 3) + digit n * digit (n + 1) * digit (n + 2) = 50 := by
  have h := Nat.mod_lt n (show 4 > 0 by norm_num)
  have e1 : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
  have e2 : (n + 2) % 4 = (n % 4 + 2) % 4 := by omega
  have e3 : (n + 3) % 4 = (n % 4 + 3) % 4 := by omega
  unfold digit
  rw [e1, e2, e3]
  interval_cases (n % 4) <;> norm_num

theorem four (n : ℕ) :
    (products (n + 4)).1 = 24 * (products n).1 ∧
    (products (n + 4)).2 = 24 * (products n).2 + 50 * (products n).1 := by
  obtain ⟨h1, h2⟩ := digit_prod n
  simp only [step]
  constructor
  · linear_combination (products n).1 * h1
  · linear_combination (products n).2 * h1 + (products n).1 * h2

theorem rec (m : ℕ) : a (m + 8) = 48 * a (m + 4) - 576 * a m := by
  obtain ⟨p1, e1⟩ := four m
  obtain ⟨p2, e2⟩ := four (m + 4)
  unfold a
  rw [e2, e1, p1]
  ring

end A203165Proof

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a203165.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [A203165Proof.rec m, show m + 8 - 4 = m + 4 by omega, show m + 8 - 8 = m by omega]
  · ext n
    have hexp : ((1 - C 24 * X ^ 4 : ℤ⟦X⟧)) ^ 2 * mk OMA.S_oeis_a203165.a =
        mk OMA.S_oeis_a203165.a - C 48 * (X ^ 4 * mk OMA.S_oeis_a203165.a) +
          C 576 * (X ^ 8 * mk OMA.S_oeis_a203165.a) := by
      have h48 : (C 48 : ℤ⟦X⟧) = 2 * C 24 := by rw [show (48 : ℤ) = 2 * 24 by norm_num, map_mul]; rfl
      have h576 : (C 576 : ℤ⟦X⟧) = C 24 * C 24 := by rw [← map_mul]; norm_num
      rw [h48, h576]
      ring
    rw [hexp]
    simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      rw [if_pos (by omega), if_pos (by omega), show m + 8 - 4 = m + 4 by omega,
        show m + 8 - 8 = m by omega, A203165Proof.rec m]
      simp
