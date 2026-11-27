import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-! Compute the first integral homology of the circle by the contractible
two-chart cover used in FrenzyMath/PoincareConjecture `IntegralSphereBase.lean`.
The leaves isolate open-cover excision/relative exactness, the antipodal
intersection geometry, and the reduced degree-zero calculation for S⁰. -/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2

open AlgebraicTopology CategoryTheory Limits
open scoped ContinuousMap EuclideanGeometry

def H1 : Prop :=
  ∃ A B : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1),
    IsOpen A ∧ IsOpen B ∧ A ∪ B = Set.univ ∧
    ContractibleSpace A ∧ ContractibleSpace B ∧
    Nonempty (↥(A ∩ B) ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)

def H2 : Prop :=
  ∀ (A B : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)),
    IsOpen A → IsOpen B → A ∪ B = Set.univ →
    ContractibleSpace A → ContractibleSpace B →
    Nonempty ((((singularHomologyFunctor AddCommGrpCat 1).obj (AddCommGrpCat.of ℤ)).obj
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))) ≅
      (CategoryTheory.Limits.kernel
        (((singularHomologyFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℤ)).map
          (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
            C(((Subtype.val : B → Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ⁻¹' A), B))))))

def H3 : Prop :=
  ∀ (A B : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)),
    ContractibleSpace B →
    Nonempty (↥(A ∩ B) ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) →
    Nonempty ((CategoryTheory.Limits.kernel
        (((singularHomologyFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℤ)).map
          (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
            C(((Subtype.val : B → Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ⁻¹' A), B)))) ≅
      CategoryTheory.Limits.kernel
        (TopCat.singularHomology₀ε
          (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) (AddCommGrpCat.of ℤ))))

def H4 : Prop :=
  Nonempty (CategoryTheory.Limits.kernel
      (TopCat.singularHomology₀ε
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) (AddCommGrpCat.of ℤ)) ≅
    AddCommGrpCat.of ℤ)

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1.H3 := by
  intro hcover hexcision htransport hzero
  obtain ⟨A, B, hA, hB, hcoverAB, hcontractA, hcontractB, hAB⟩ := hcover
  obtain ⟨eCover⟩ := hexcision A B hA hB hcoverAB hcontractA hcontractB
  obtain ⟨eTransport⟩ := htransport A B hcontractB hAB
  obtain ⟨eZero⟩ := hzero
  exact ⟨eCover ≪≫ eTransport ≪≫ eZero⟩

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2
