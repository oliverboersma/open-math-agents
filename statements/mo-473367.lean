import Mathlib

/-!
# MathOverflow 473367

Source: https://mathoverflow.net/questions/473367
-/

namespace OMA.S_mo_473367

open Finset Matrix

def Laplacian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal (fun i => ∑ j, A i j) - A

def quadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * ((Laplacian A) i j : ℝ) * x j

theorem main : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
    (∀ i, A i i = 0) → (∀ i j, A i j = A j i) →
    (∀ i j, i ≠ j → A i j = -1 ∨ A i j = 1) →
    (∀ S : Finset (Fin n), S.Nonempty → S ≠ univ →
      0 ≤ ∑ i ∈ S, ∑ j ∈ univ \ S, A i j) →
    ∀ x : Fin n → ℝ, 0 ≤ quadraticForm A x := by
  sorry

end OMA.S_mo_473367
