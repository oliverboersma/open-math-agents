import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1_H2_R1
import Mathlib

-- Step PoincareConjecture.poincare_conjecture.R1.H1.R1.H1.R1.H2.R1.H3: hypothesis H3 of reduction
-- PoincareConjecture.poincare_conjecture.R1.H1.R1.H1.R1.H2.R1
-- Credit: @ivillar

/-!
A contractible space is homotopy equivalent to a point, whose singular homology vanishes in
positive degrees (Mathlib: totally disconnected spaces), so `H_k(X) = 0` for `k ≥ 1`. In the long
exact sequence of the pair, the connecting map `H_n(X, A) → H_{n-1}(A)` sits between `H_n(X)`
and `H_{n-1}(X)`, both zero for `n ≥ 2`, hence it is an isomorphism
(`ShortComplex.ShortExact.isIso_δ`).
-/

open CategoryTheory Limits AlgebraicTopology
open scoped ContinuousMap

namespace OMA.PoincareConnecting

theorem homology_iso_of_hequiv (n : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) :
    Nonempty ((((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of X)) ≅ (((singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).obj (TopCat.of Y))) := by
  let F := (singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  refine ⟨⟨F.map f, F.map g, ?_, ?_⟩⟩
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.left_inv
    have hh : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := h
    exact hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.right_inv
    have hh : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := h
    exact hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n

theorem isZero_contractible (X : Type) [TopologicalSpace X] [ContractibleSpace X] (k : ℕ)
    (hk : k ≠ 0) :
    IsZero ((((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of X)).homology k) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  obtain ⟨φ⟩ := homology_iso_of_hequiv k e
  have h0 : IsZero (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of Unit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace AddCommGrpCat k
      (AddCommGrpCat.of ℤ) (TopCat.of Unit) hk
  exact h0.of_iso φ

end OMA.PoincareConnecting

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1_H2_R1.H3 := by
  unfold OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1_H2_R1.H3
  intro X _ A _ n hn C i S hS
  apply hS.isIso_δ
  · exact OMA.PoincareConnecting.isZero_contractible X n (by omega)
  · exact OMA.PoincareConnecting.isZero_contractible X (n - 1) (by omega)
