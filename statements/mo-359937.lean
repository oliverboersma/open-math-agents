import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# Cubic symmetry of irreducible orthogonal matrices

Source: https://mathoverflow.net/questions/359937
Credit: @eliayousf

This is the revised question in Edit 2. Both the row identities and the
column identities from the first edit are retained. Following the
discussion of arbitrary row and column permutations, irreducible means
that the rows and columns cannot be independently partitioned into
corresponding nontrivial square blocks with zeros outside those blocks.
-/

namespace OMA.S_mo_359937

def HasBlockDecomposition {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ S T : Finset (Fin n), S.Nonempty ∧ S.card < n ∧ S.card = T.card ∧
    ∀ i j, ((i ∈ S ∧ j ∉ T) ∨ (i ∉ S ∧ j ∈ T)) → A i j = 0

theorem main : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    A * A.transpose = 1 → A.transpose * A = 1 →
    ¬ HasBlockDecomposition A →
    (∀ i j, ∑ k, A i k ^ 3 * A j k = ∑ k, A j k ^ 3 * A i k) →
    (∀ i j, ∑ k, A k i ^ 3 * A k j = ∑ k, A k j ^ 3 * A k i) →
    ∀ i j k l, A i j ≠ 0 → A k l ≠ 0 → |A i j| = |A k l| := by
  sorry

end OMA.S_mo_359937
