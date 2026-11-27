import OMAStatements.S_oeis_a057300
import Mathlib

open OMA.S_oeis_a057300

lemma OMA.unf (n : ℕ) (h : n ≠ 0) : a n = 4 * a (n / 4) + swapDigit (n % 4) := by
  rw [a]; simp [h]

theorem OMA.solution : type_of% @OMA.S_oeis_a057300.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨by simp [a], ?_⟩
      rw [OMA.unf 1 (by norm_num)]; simp [a, swapDigit]
    · have h2 := ih (n / 2) (by omega)
      have hA : a (2 * n) = 4 * a (n / 2) + swapDigit ((2 * n) % 4) := by
        rw [OMA.unf _ (by omega), show 2 * n / 4 = n / 2 by omega]
      have hB : a (2 * n + 1) = 4 * a (n / 2) + swapDigit ((2 * n + 1) % 4) := by
        rw [OMA.unf _ (by omega), show (2 * n + 1) / 4 = n / 2 by omega]
      have hC : a n = 4 * a (n / 4) + swapDigit (n % 4) := OMA.unf _ (by omega)
      rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
      · rw [show 2 * m / 2 = m by omega] at h2 hA hB
        rw [show 2 * m / 4 = m / 2 by omega, show 2 * m % 4 = 2 * (m % 2) by omega] at hC
        rw [show 2 * (2 * m) % 4 = 0 by omega] at hA
        rw [show (2 * (2 * m) + 1) % 4 = 1 by omega] at hB
        simp only [swapDigit] at hA hB hC
        rcases Nat.mod_two_eq_zero_or_one m with e | e <;> rw [e] at hC <;> norm_num at hA hB hC <;>
          constructor <;> omega
      · rw [show (2 * m + 1) / 2 = m by omega] at h2 hA hB
        rw [show (2 * m + 1) / 4 = m / 2 by omega,
          show (2 * m + 1) % 4 = 2 * (m % 2) + 1 by omega] at hC
        rw [show 2 * (2 * m + 1) % 4 = 2 by omega] at hA
        rw [show (2 * (2 * m + 1) + 1) % 4 = 3 by omega] at hB
        simp only [swapDigit] at hA hB hC
        rcases Nat.mod_two_eq_zero_or_one m with e | e <;> rw [e] at hC <;> norm_num at hA hB hC <;>
          constructor <;> omega
