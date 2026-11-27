import FormalConjectures.GreensOpenProblems.«68»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Green68_green_68_variants_voloch_R1
open Green68 MvPolynomial

/-- The local six-point conic criterion for an arc of Voloch's size. -/
def H1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ A : Finset (Fin 2 → ZMod p),
    MeetsLinesInAtMost 2 A → (44 : ℝ) / 45 * p + 8 / 9 < A.card →
    ∀ S ⊆ A, S.card ≤ 6 → ∃ F : MvPolynomial (Fin 2) (ZMod p),
      F ≠ 0 ∧ F.totalDegree ≤ 2 ∧ ∀ a ∈ S, eval a F = 0

/-- A finite configuration lies on one conic once every subset of at most six
points lies on some conic. Six is the dimension of the space of plane quadrics. -/
def H2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Finset (Fin 2 → ZMod p)),
    (∀ S ⊆ A, S.card ≤ 6 → ∃ F : MvPolynomial (Fin 2) (ZMod p),
      F ≠ 0 ∧ F.totalDegree ≤ 2 ∧ ∀ a ∈ S, eval a F = 0) →
    ∃ F : MvPolynomial (Fin 2) (ZMod p),
      F ≠ 0 ∧ F.totalDegree ≤ 2 ∧ ∀ a ∈ A, eval a F = 0

theorem main : H1 → H2 → type_of% @Green68.green_68.variants.voloch := by
  intro six combine p _ hp A harc hsize
  exact combine p A (six p hp A harc hsize)

end OMA.R_Green68_green_68_variants_voloch_R1
