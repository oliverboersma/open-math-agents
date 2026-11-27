import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Complementary nonsingular minors

Lchencz asked for a classification of square matrices for which every pair of
complementary square minors has product zero. Will Sawin observed that a
rectangle with the rank defect on the right suffices, in comment 1319622.
The converse follows by applying Edmonds' matroid partition theorem to the
column matroid of the block matrix formed by adjoining the identity to A.

Source: https://mathoverflow.net/questions/506603 (CC BY-SA 4.0).
-/

namespace OMA.S_mo_506603

/-- Rank of the submatrix on a chosen set of rows and columns. -/
noncomputable def submatrixRank {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (R C : Finset (Fin n)) : ℕ :=
  (A.submatrix (fun i : R => (i : Fin n)) (fun j : C => (j : Fin n))).rank

/-- A square matrix over a field has a singular member in every pair of
complementary square submatrices exactly when some rectangular submatrix
has twice its rank strictly below its row count plus its column count minus n.
The rank test for singularity avoids choosing an order on the selected indices.
-/
theorem main : ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    (∀ R C : Finset (Fin n), R.card = C.card →
      submatrixRank A R C < R.card ∨ submatrixRank A Rᶜ Cᶜ < Rᶜ.card) ↔
    ∃ R C : Finset (Fin n), n + 2 * submatrixRank A R C < R.card + C.card := by
  sorry

end OMA.S_mo_506603
