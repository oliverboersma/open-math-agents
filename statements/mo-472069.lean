import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Normality and small doubling

Source: https://mathoverflow.net/questions/472069
Credit: @eliayousf

A subset is a union of left cosets of a subgroup if it contains xH
whenever it contains x. The pointwise Finset product A * A is A².
Maximality is with respect to inclusion among subgroups with the stated
coset property.
-/

open scoped Pointwise

namespace OMA.S_mo_472069

def UnionLeftCosets {G : Type*} [Group G] (S : Set G) (H : Subgroup G) : Prop :=
  ∀ x ∈ S, ∀ h ∈ H, x * h ∈ S

theorem main : ∀ (G : Type) [Group G] [DecidableEq G] (A : Finset G) (H : Subgroup G),
    Subgroup.closure (A : Set G) = ⊤ →
    UnionLeftCosets ((A * A : Finset G) : Set G) H →
    (∀ K : Subgroup G, H ≤ K → UnionLeftCosets ((A * A : Finset G) : Set G) K → K ≤ H) →
    (A * A).card < 2 * A.card → H.Normal := by
  sorry

end OMA.S_mo_472069
