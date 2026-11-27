import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

/-!
# Comparing centralities before and after an edge edit

Source: https://mathoverflow.net/questions/200855
Credit: @Spinausore

A Boolean adjacency matrix, its symmetry, and its zero diagonal describe a
finite simple undirected graph. The distinguished vertices a, b, c are the
vertices called 1, 2, 3 in the question. Both edits change a symmetric pair.
-/

namespace OMA.S_mo_200855

def realAdj {n : ℕ} (G : Fin n → Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => if G i j then 1 else 0)

def edit {n : ℕ} (G : Fin n → Fin n → Bool) (a b : Fin n) (v : Bool)
    (i j : Fin n) : Bool :=
  if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then v else G i j

noncomputable def score {n : ℕ} (G : Fin n → Fin n → Bool) (t : ℝ) : Fin n → ℝ :=
  ((1 - t • realAdj G)⁻¹).mulVec (fun _ => 1)

theorem main : ∀ (n : ℕ), 3 ≤ n → ∀ (G : Fin n → Fin n → Bool) (a b c : Fin n) (t : ℝ),
    (∀ i j, G i j = G j i) → (∀ i, G i i = false) →
    a ≠ b → a ≠ c → b ≠ c → G a b = true → G a c = true → G b c = false →
    0 < t → t < 1 / ((n : ℝ) - 1) →
    score G t b ≤ score G t a → score G t c ≤ score G t a →
    score (edit G a b false) t a / score G t a >
      score G t c / score (edit G b c true) t c := by
  sorry

end OMA.S_mo_200855
