import OMAReductions.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1
import Mathlib

-- Step LatinSquare.oddOrderLeq9LatinSquareTransversal.R1.H3: hypothesis H3 of reduction LatinSquare.oddOrderLeq9LatinSquareTransversal.R1
-- Credit: @ivillar (original proof).
-- Strategy. Let alpha be row 0 and beta the column alpha^-1(0) (both bijections). Then
-- M i j = L (beta^-1 i) (alpha^-1 j) is normalized, and a transversal sigma of M gives the
-- transversal r -> alpha^-1 (sigma (beta r)) of L.

theorem OMA.solution : OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1.H3 := by
  intro n _ L
  let α : Fin n ≃ Fin n := Equiv.ofBijective (L.mat 0)
    ⟨L.row_injective 0, Finite.surjective_of_injective (L.row_injective 0)⟩
  let c0 : Fin n := α.symm 0
  let β : Fin n ≃ Fin n := Equiv.ofBijective (fun i => L.mat i c0)
    ⟨L.col_injective c0, Finite.surjective_of_injective (L.col_injective c0)⟩
  have hα : ∀ j, L.mat 0 j = α j := fun j => rfl
  have hβ : ∀ i, L.mat i c0 = β i := fun i => rfl
  have hβ0 : β.symm 0 = 0 := by
    rw [Equiv.symm_apply_eq, ← hβ, hα]
    exact (α.apply_symm_apply 0).symm
  let M : LatinSquare n :=
    { mat := fun i j => L.mat (β.symm i) (α.symm j)
      row_injective := fun i => (L.row_injective (β.symm i)).comp α.symm.injective
      col_injective := fun j => by
        have h := L.col_injective (α.symm j)
        intro a b hab
        exact β.symm.injective (h hab) }
  refine ⟨M, fun i => ?_, fun i => ?_, ?_⟩
  · show L.mat (β.symm 0) (α.symm i) = i
    rw [hβ0, hα, α.apply_symm_apply]
  · show L.mat (β.symm i) (α.symm 0) = i
    rw [hβ, β.apply_symm_apply]
  · rintro ⟨σ, hσ1, hσ2⟩
    refine ⟨fun r => α.symm (σ (β r)), ?_, ?_⟩
    · intro a b hab
      exact β.injective (hσ1 (α.symm.injective hab))
    · intro a b hab
      have h : M.mat (β a) (σ (β a)) = M.mat (β b) (σ (β b)) := by
        show L.mat (β.symm (β a)) (α.symm (σ (β a))) = L.mat (β.symm (β b)) (α.symm (σ (β b)))
        rw [β.symm_apply_apply, β.symm_apply_apply]
        exact hab
      exact β.injective (hσ2 h)
