import FormalConjectures.Other.HyperbolicGroupsResiduallyFinite

-- Reduction HyperbolicGroupsResiduallyFinite.hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top.R1
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Residual finiteness of hyperbolic groups, split into its two implications

Kapovich and Wise proved that the question "is every hyperbolic group residually finite?" is
equivalent to the question "does every nontrivial hyperbolic group have a proper subgroup of
finite index?".  Each of the two questions was later answered negatively, but the equivalence
itself is a theorem of its own, with two directions of very different content:

* `H1` (residual finiteness everywhere forces a proper finite-index subgroup in every nontrivial
  hyperbolic group) is the direction that uses residual finiteness directly: a nontrivial
  hyperbolic group is residually finite, so some finite quotient separates a nontrivial element
  from the identity, and the kernel of that quotient is a proper finite-index subgroup.

* `H2` (a proper finite-index subgroup in every nontrivial hyperbolic group forces residual
  finiteness) is the converse, and it is the harder direction: it needs that finite-index
  subgroups of hyperbolic groups are again hyperbolic, so that one can pass to a subgroup
  separating a given element and iterate the hypothesis inside it.

Neither direction is in Mathlib, and neither is a formal consequence of the other.  Together they
are the statement, and the assembly is formal.
-/

namespace OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top_R1

/-- The forward direction: if every hyperbolic group is residually finite, then every nontrivial
hyperbolic group has a proper subgroup of finite index. -/
def H1 : Prop :=
  (∀ (G : Type) [Group G] [Group.IsHyperbolic G], Group.ResiduallyFinite G) →
    ∀ (G : Type) [Group G] [Group.IsHyperbolic G] [Nontrivial G],
      ∃ H : Subgroup G, H ≠ ⊤ ∧ H.FiniteIndex

/-- The converse direction: if every nontrivial hyperbolic group has a proper subgroup of finite
index, then every hyperbolic group is residually finite. -/
def H2 : Prop :=
  (∀ (G : Type) [Group G] [Group.IsHyperbolic G] [Nontrivial G],
      ∃ H : Subgroup G, H ≠ ⊤ ∧ H.FiniteIndex) →
    ∀ (G : Type) [Group G] [Group.IsHyperbolic G], Group.ResiduallyFinite G

theorem main : H1 → H2 →
    type_of% @HyperbolicGroupsResiduallyFinite.hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top_R1
