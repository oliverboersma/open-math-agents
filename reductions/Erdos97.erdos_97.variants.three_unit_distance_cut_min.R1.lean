import FormalConjectures.ErdosProblems.«97»

/-! Construction and exclusion for the Fishburn–Reeds cut minimum. -/

open Erdos97 EuclideanGeometry
open scoped Classical EuclideanGeometry

namespace OMA.R_Erdos97_erdos_97_variants_three_unit_distance_cut_min_R1

/-- Construct a twenty-vertex convex set with a cut having three unit neighbors
on the opposite side at every vertex. -/
def H1 : Prop :=
  ∃ V A B : Finset ℝ², 20 = V.card ∧ ConvexIndep V ∧ A.Nonempty ∧ B.Nonempty ∧
    IsCut V A B ∧ HasNUnitDistancePointsOn 3 B A ∧ HasNUnitDistancePointsOn 3 A B

/-- Exclude all such configurations with fewer than twenty vertices. -/
def H2 : Prop :=
  ∀ V A B : Finset ℝ², ConvexIndep V → A.Nonempty → B.Nonempty →
    IsCut V A B → HasNUnitDistancePointsOn 3 B A → HasNUnitDistancePointsOn 3 A B →
    20 ≤ V.card

theorem main : H1 → H2 → type_of% @Erdos97.erdos_97.variants.three_unit_distance_cut_min := by
  intro h₁ h₂
  refine le_antisymm (Nat.sInf_le h₁) (le_csInf ⟨20, h₁⟩ ?_)
  rintro n ⟨V, A, B, rfl, hV, hA, hB, hcut, hAB, hBA⟩
  exact h₂ V A B hV hA hB hcut hAB hBA

end OMA.R_Erdos97_erdos_97_variants_three_unit_distance_cut_min_R1