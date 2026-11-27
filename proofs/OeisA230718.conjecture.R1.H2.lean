import OMAReductions.R_OeisA230718_conjecture_R1
import Mathlib

/-!
# A prefix bound for consecutive powers

Shift the prefix by two places to compare its sum with the whole sum.
The last-pair hypothesis then bounds the whole sum by twice the endpoint power.
The first proof of this step was submitted by @ivillar in PR #7727.
-/

open Finset

private theorem prefix_bound (n M : ℕ) (hn : 0 < n)
    (hpair : (M + 1) ^ n + M ^ n ≤ (M + 2) ^ n) :
    (∑ i ∈ range (M + 2), i ^ n) < 2 * (M + 2) ^ n := by
  let P := ∑ i ∈ range M, i ^ n
  let A := (M + 2) ^ n
  let C := M ^ n
  let S := ∑ i ∈ range (M + 2), i ^ n
  have hS : S = P + C + (M + 1) ^ n := by
    simp only [S, Finset.sum_range_succ (n := M + 1), Finset.sum_range_succ (n := M)]
    rfl
  have hshift : (∑ i ∈ range M, (i + 2) ^ n) ≤ S := by
    dsimp only [S]
    rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun i : ℕ => (i + 1) ^ n) M]
    exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hmul : A * P ≤ C * S := by
    calc
      A * P = ∑ i ∈ range M, A * i ^ n := Finset.mul_sum ..
      _ ≤ ∑ i ∈ range M, C * (i + 2) ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        have hiM := Finset.mem_range.mp hi
        dsimp only [A, C]
        rw [← mul_pow, ← mul_pow]
        apply Nat.pow_le_pow_left
        simp only [Nat.add_mul, Nat.mul_add]
        omega
      _ = C * (∑ i ∈ range M, (i + 2) ^ n) := (Finset.mul_sum ..).symm
      _ ≤ C * S := Nat.mul_le_mul_left C hshift
  change (M + 1) ^ n + C ≤ A at hpair
  have hP : S ≤ P + A := by omega
  have hC : 2 * C < A := by
    have hlt : C < (M + 1) ^ n := Nat.pow_lt_pow_left (by omega) hn.ne'
    omega
  change S < 2 * A
  by_contra! h
  have hPA : A ≤ P := by omega
  have hPpos : 0 < P := lt_of_lt_of_le (by dsimp only [A]; positivity) hPA
  have hCS : C * S ≤ (2 * C) * P := by
    calc
      C * S ≤ C * (2 * P) := Nat.mul_le_mul_left C (by omega)
      _ = (2 * C) * P := by ring
  exact (not_lt_of_ge (hmul.trans hCS)) (Nat.mul_lt_mul_of_pos_right hC hPpos)

theorem OMA.solution : OMA.R_OeisA230718_conjecture_R1.H2 := by
  intro n N hn hN _ hpair
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  apply prefix_bound n M (by omega)
  have h₁ : M + 2 - 1 = M + 1 := by omega
  have h₂ : M + 2 - 2 = M := by omega
  simpa only [h₁, h₂] using hpair
