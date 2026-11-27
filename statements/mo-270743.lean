import Mathlib

/-!
# MathOverflow 270743

Source: https://mathoverflow.net/questions/270743
-/

namespace OMA.S_mo_270743

open Finset Matrix

noncomputable def rowEnergy {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) : ℝ :=
  ∑ j, (A i j) ^ 2

def retain {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun i j => if i ∈ S then A i j else 0

noncomputable def squaredFrobenius {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i, rowEnergy A i

theorem main : ∀ n m s : ℕ, n < m → s ≤ n → ∀ A : Matrix (Fin n) (Fin m) ℝ,
    ∃ S : Finset (Fin n), S.card = s ∧
      (∀ i ∈ S, ∀ j ∉ S, rowEnergy A j ≤ rowEnergy A i) ∧
      ∀ T : Finset (Fin n), T.card = s →
        squaredFrobenius (A - retain A S) ≤ squaredFrobenius (A - retain A T) := by
  sorry

end OMA.S_mo_270743
