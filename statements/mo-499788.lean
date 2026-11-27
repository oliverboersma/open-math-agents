import Mathlib

/-!
# Off-diagonal entries of the square root of a tree's biadjacency Gram matrix

Source: https://mathoverflow.net/questions/499788
Credit: @zarnab222-dev

For a finite tree with a specified bipartition, the author asks whether every off-diagonal
entry of the positive semidefinite square root of the row Gram matrix has magnitude
strictly less than one. The two vertex classes are indexed by `Fin m` and `Fin n`.
-/

namespace OMA.S_mo_499788

open scoped MatrixOrder

/-- The rectangular zero-one adjacency matrix from the left vertex class to the right. -/
noncomputable def biadj {m n : ℕ} (G : SimpleGraph (Fin m ⊕ Fin n)) :
    Matrix (Fin m) (Fin n) ℝ := by
  classical
  exact fun i j => if G.Adj (.inl i) (.inr j) then 1 else 0

theorem main :
    ∀ (m n : ℕ) (G : SimpleGraph (Fin m ⊕ Fin n)), G.IsTree →
      (∀ i j : Fin m, ¬G.Adj (.inl i) (.inl j)) →
      (∀ u v : Fin n, ¬G.Adj (.inr u) (.inr v)) →
      ∀ i j : Fin m, i ≠ j →
        |(CFC.sqrt (biadj G * (biadj G).transpose)) i j| < 1 := by
  sorry

end OMA.S_mo_499788
