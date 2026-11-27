import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1
import Mathlib

-- Step PoincareConjecture.poincare_conjecture.R1.H1.R1.H2.R1.H2.R1.H1: hypothesis H1 of reduction
-- PoincareConjecture.poincare_conjecture.R1.H1.R1.H2.R1.H2.R1
-- Credit: @ivillar

/-!
Let `A ⊆ X` be contractible and `i : C(A) → C(X)` the induced (degreewise injective) chain map.
Since `id_A` is homotopic to a constant map `A → {y}`, the constant map `r : X → A` at `y`
satisfies `r ∘ i ≃ id_A`, so `H_k(i)` is split mono in every degree. Also `H_k(A) = 0` for
`k ≥ 1` (homotopy invariance and the homology of a point). In the long exact sequence of the
pair, `H_n(X) → H_n(X, A)` is mono because `H_n(A) = 0`, and epi because the connecting map
`H_n(X, A) → H_{n-1}(A)` vanishes, `H_{n-1}(A) → H_{n-1}(X)` being mono.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped ContinuousMap

namespace OMA.PoincareCollapse

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

theorem chains_mono {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    Mono ((((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ TopCat.of X)).f n) := by
  have h1 : Mono (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of A ⟶ TopCat.of X) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  have h2 : Mono (TopCat.toSSet.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of A ⟶ TopCat.of X)) := inferInstance
  have h3 : Mono ((TopCat.toSSet.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of A ⟶ TopCat.of X)).app (Opposite.op (SimplexCategory.mk n))) := inferInstance
  exact (sigmaConst.obj (AddCommGrpCat.of ℤ)).map_mono _

theorem homology_mono {X : Type} [TopologicalSpace X] (A : Set X) [ContractibleSpace A] (k : ℕ) :
    Mono (HomologicalComplex.homologyMap
      (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ TopCat.of X)) k) := by
  obtain ⟨y, ⟨H⟩⟩ := id_nullhomotopic A
  let r : TopCat.of X ⟶ TopCat.of A := TopCat.ofHom (ContinuousMap.const X y)
  have hh : TopCat.Homotopy
      ((TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ TopCat.of X) ≫ r)
      (𝟙 (TopCat.of A)) := H.symm
  have h1 := hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) k
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.homologyMap_comp,
    CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] at h1
  exact mono_of_mono_fac h1

end OMA.PoincareCollapse

open OMA.PoincareCollapse in
theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1.H1 := by
  unfold OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1.H1
  intro X _ A _ n hn C i
  have hmono : Mono i := HomologicalComplex.mono_of_mono_f _ (fun k => chains_mono A k)
  have hS : (ShortComplex.cokernelSequence i).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _, mono_f := hmono }
  have hz : IsZero ((C.obj (TopCat.of A)).homology n) := isZero_contractible A n (by omega)
  have hrel : (ComplexShape.down ℕ).Rel n (n - 1) := by
    show n - 1 + 1 = n
    omega
  have hmg : Mono (HomologicalComplex.homologyMap (cokernel.π i) n) := by
    apply (hS.homology_exact₂ n).mono_g
    exact hz.eq_of_src _ _
  have heg : Epi (HomologicalComplex.homologyMap (cokernel.π i) n) := by
    apply (hS.homology_exact₃ n (n - 1) hrel).epi_f
    have hm : Mono (HomologicalComplex.homologyMap i (n - 1)) := homology_mono A (n - 1)
    exact (hS.homology_exact₁ n (n - 1) hrel).mono_g_iff.mp hm
  exact isIso_of_mono_of_epi _
