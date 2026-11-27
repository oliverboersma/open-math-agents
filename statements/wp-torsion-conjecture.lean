import Mathlib

/-!
# Torsion conjecture

Source: https://en.wikipedia.org/wiki/Torsion_conjecture
Source text license: CC BY-SA 4.0
Credit: @menelikbaye-digitalmethod

This states the source's fixed-number-field formulation: the bound depends
only on the number field and the dimension, and is uniform in the abelian variety.
An abelian variety is represented as a proper geometrically integral group scheme.
Its rational points are morphisms over the base field from the terminal scheme.
The extended natural cardinality bound also requires the torsion set to be finite.
-/

namespace OMA.S_wp_torsion_conjecture

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

theorem main :
    ∀ (K : Type u) [Field K] [NumberField K] (g : ℕ),
      ∃ B : ℕ,
        ∀ (A : Over (Spec (CommRingCat.of K))) [GrpObj A]
          [IsProper A.hom] [GeometricallyIntegral A.hom],
          topologicalKrullDim A.left = (g : WithBot ℕ∞) →
          ({P : (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A) | IsOfFinOrder P} : Set _).encard
            ≤ (B : ℕ∞) := by
  sorry

end OMA.S_wp_torsion_conjecture
