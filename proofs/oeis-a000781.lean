import OMAStatements.S_oeis_a000781
import Mathlib

/-!
# Proof of OEIS-A000781 conjecture

Credit: @AkiRA-COM-FP
-/

open OMA.S_oeis_a000781

private theorem catalan_step (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < n + 1)
  calc
    (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (n + 1).centralBinom := by
      rw [← succ_mul_catalan_eq_centralBinom (n + 1)]
    _ = 2 * (2 * n + 1) * n.centralBinom := Nat.succ_mul_centralBinom_succ n
    _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
      rw [← succ_mul_catalan_eq_centralBinom n]
      ring

private theorem catalan_step_int (n : ℕ) :
    ((n : ℤ) + 2) * (catalan (n + 1) : ℤ) =
      2 * (2 * (n : ℤ) + 1) * (catalan n : ℤ) := by
  exact_mod_cast catalan_step n

private theorem catalan_le_succ (n : ℕ) : catalan n ≤ catalan (n + 1) := by
  apply Nat.le_of_mul_le_mul_left _ (by omega : 0 < n + 2)
  rw [catalan_step]
  exact Nat.mul_le_mul_right _ (by omega)

private theorem catalan_positive (n : ℕ) : 0 < catalan n := by
  induction n with
  | zero => simp [catalan_zero]
  | succ n ih => exact lt_of_lt_of_le ih (catalan_le_succ n)

private theorem cast_a_succ (n : ℕ) :
    (a (n + 1) : ℤ) = 3 * (catalan (n + 1) : ℤ) - (catalan n : ℤ) - 1 := by
  have hle := catalan_le_succ n
  have hpos := catalan_positive (n + 1)
  have hsub : catalan n ≤ 3 * catalan (n + 1) := by omega
  have hone : 1 ≤ 3 * catalan (n + 1) - catalan n := by omega
  simp only [a, Nat.add_sub_cancel, Int.ofNat_sub hone, Int.ofNat_sub hsub]
  push_cast
  rfl

theorem OMA.solution : type_of% @OMA.S_oeis_a000781.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
  rw [cast_a_succ (m + 4), cast_a_succ (m + 3), cast_a_succ (m + 2),
    cast_a_succ (m + 1), cast_a_succ m]
  have h0 := catalan_step_int m
  have h1 := catalan_step_int (m + 1)
  have h2 := catalan_step_int (m + 2)
  have h3 := catalan_step_int (m + 3)
  have h4 := catalan_step_int (m + 4)
  push_cast at h1 h2 h3 h4 ⊢
  linear_combination 9 * h4 - 24 * h3 + 22 * h2 - 8 * h1 + h0
