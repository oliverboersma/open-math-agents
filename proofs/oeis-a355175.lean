import OMAStatements.S_oeis_a355175
import Mathlib

namespace A355175Proof
open OMA.S_oeis_a355175

def U (n : ℕ) : Matrix (Fin n) (Fin 3) ℚ :=
  fun i b => ![(i.val : ℚ)^2, -2 * (i.val : ℚ), 1] b

def V (n : ℕ) : Matrix (Fin 3) (Fin n) ℚ :=
  fun c j => ![1, (j.val : ℚ), (j.val : ℚ)^2] c

lemma decomp' (n : ℕ) : quadraticToeplitz n = 1 + U n * V n := by
  ext i j
  simp only [quadraticToeplitz, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
    Fin.sum_univ_three, U, V]
  simp
  ring

lemma s0 (n : ℕ) : ∑ _j : Fin n, (1 : ℚ) = n := by simp

lemma s1 (n : ℕ) : ∑ j : Fin n, (j.val : ℚ) = (n : ℚ) * (n - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (j : ℚ)) n]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma s2 (n : ℕ) : ∑ j : Fin n, (j.val : ℚ)^2 = (n : ℚ) * (n - 1) * (2 * n - 1) / 6 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (j : ℚ)^2) n]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma s3 (n : ℕ) : ∑ j : Fin n, (j.val : ℚ)^3 = (n : ℚ)^2 * (n - 1)^2 / 4 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (j : ℚ)^3) n]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma s4 (n : ℕ) : ∑ j : Fin n, (j.val : ℚ)^4
    = (n : ℚ) * (n - 1) * (2 * n - 1) * (3 * n^2 - 3 * n - 1) / 30 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (j : ℚ)^4) n]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma e00 (n : ℕ) : (V n * U n) 0 0 = (n : ℚ) * (n - 1) * (2 * n - 1) / 6 := by
  rw [← s2 n, Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun j _ => by simp [U, V])

lemma e01 (n : ℕ) : (V n * U n) 0 1 = -2 * ((n : ℚ) * (n - 1) / 2) := by
  rw [← s1 n, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by simp [U, V])

lemma e02 (n : ℕ) : (V n * U n) 0 2 = (n : ℚ) := by
  rw [← s0 n, Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun j _ => by simp [U, V])

lemma e10 (n : ℕ) : (V n * U n) 1 0 = (n : ℚ)^2 * (n - 1)^2 / 4 := by
  rw [← s3 n, Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun j _ => by simp [U, V]; ring)

lemma e11 (n : ℕ) : (V n * U n) 1 1 = -2 * ((n : ℚ) * (n - 1) * (2 * n - 1) / 6) := by
  rw [← s2 n, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by simp [U, V]; ring)

lemma e12 (n : ℕ) : (V n * U n) 1 2 = (n : ℚ) * (n - 1) / 2 := by
  rw [← s1 n, Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun j _ => by simp [U, V])

lemma e20 (n : ℕ) : (V n * U n) 2 0
    = (n : ℚ) * (n - 1) * (2 * n - 1) * (3 * n^2 - 3 * n - 1) / 30 := by
  rw [← s4 n, Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun j _ => by simp [U, V]; ring)

lemma e21 (n : ℕ) : (V n * U n) 2 1 = -2 * ((n : ℚ)^2 * (n - 1)^2 / 4) := by
  rw [← s3 n, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by simp [U, V]; ring)

lemma e22 (n : ℕ) : (V n * U n) 2 2 = (n : ℚ) * (n - 1) * (2 * n - 1) / 6 := by
  rw [← s2 n, Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun j _ => by simp [U, V])

end A355175Proof

open OMA.S_oeis_a355175 A355175Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a355175.main := by
  intro n
  unfold a
  rw [decomp', Matrix.det_one_add_mul_comm, Matrix.det_fin_three]
  simp only [Matrix.add_apply, e00, e01, e02, e10, e11, e12, e20, e21, e22, Matrix.one_apply]
  simp
  ring
