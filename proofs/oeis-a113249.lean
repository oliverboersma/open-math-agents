import OMAStatements.S_oeis_a113249
import Mathlib.Tactic

/-!
The odd-indexed terms are the squares of an integer sequence with a
second-order recurrence. To compare them, eliminate the odd shifts
from the defining fourth-order recurrence. Its odd terms and the
candidate squares then satisfy the same third-order recurrence.
-/
-- Credit: @dk8827

namespace OMA.A113249

open OMA.S_oeis_a113249

private def root (m : ℕ) : ℕ → ℤ
  | 0 => 2
  | 1 => (m : ℤ) ^ 2 - 8
  | n + 2 => -4 * root m (n + 1) - (m : ℤ) ^ 2 * root m n

private theorem original_recurrence (m i : ℕ) :
    a m (i + 4) + 4 * a m (i + 3) - 4 * (m : ℤ) ^ 2 * a m (i + 1) -
      (m : ℤ) ^ 4 * a m i = 0 := by
  rw [a]
  ring

private theorem stride_recurrence (m i : ℕ) :
    a m (i + 6) = (16 - (m : ℤ) ^ 2) * a m (i + 4) +
      ((m : ℤ) ^ 4 - 16 * (m : ℤ) ^ 2) * a m (i + 2) + (m : ℤ) ^ 6 * a m i := by
  have h0 := original_recurrence m i
  have h1 := original_recurrence m (i + 1)
  have h2 := original_recurrence m (i + 2)
  linear_combination h2 - 4 * h1 + (m : ℤ) ^ 2 * h0

private theorem square_recurrence (m n : ℕ) :
    root m (n + 3) ^ 2 = (16 - (m : ℤ) ^ 2) * root m (n + 2) ^ 2 +
      ((m : ℤ) ^ 4 - 16 * (m : ℤ) ^ 2) * root m (n + 1) ^ 2 +
      (m : ℤ) ^ 6 * root m n ^ 2 := by
  rw [show root m (n + 3) = -4 * root m (n + 2) - (m : ℤ) ^ 2 * root m (n + 1) by rfl,
    show root m (n + 2) = -4 * root m (n + 1) - (m : ℤ) ^ 2 * root m n by rfl]
  ring

private theorem odd_term_eq_square (m n : ℕ) :
    a m (2 * n + 1) = root m n ^ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 3
    · interval_cases n <;> norm_num [a, root] <;> ring
    · let j := n - 3
      have hj : n = j + 3 := by dsimp [j]; omega
      have h0 := ih j (by omega)
      have h1 := ih (j + 1) (by omega)
      have h2 := ih (j + 2) (by omega)
      have hstep := stride_recurrence m (2 * j + 1)
      rw [show 2 * j + 1 + 6 = 2 * (j + 3) + 1 by omega,
        show 2 * j + 1 + 4 = 2 * (j + 2) + 1 by omega,
        show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega, h0, h1, h2] at hstep
      rw [hj, hstep, square_recurrence]

theorem solution_aux (m n : ℕ) : IsSquare (a m (2 * n + 1)) :=
  ⟨root m n, by rw [odd_term_eq_square, pow_two]⟩

end OMA.A113249

theorem OMA.solution : type_of% @OMA.S_oeis_a113249.main := OMA.A113249.solution_aux
