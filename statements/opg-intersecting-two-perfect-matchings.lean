import Mathlib

/-!
# The intersection of two perfect matchings

Source: https://www.openproblemgarden.org/op/intersecting_two_perfect_matchings
Credit: @LAPRAI

Conjecture: every bridgeless cubic graph has two perfect matchings `M₁, M₂` so that `M₁ ∩ M₂`
does not contain an odd edge-cut.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s; cubic means `IsRegularOfDegree 3`; bridgeless means
  no edge is a bridge (Mathlib's `SimpleGraph.IsBridge`).
* A perfect matching is a Mathlib subgraph `M` with `M.IsPerfectMatching`; `M₁ ∩ M₂` is the
  intersection of their edge sets.
* The edge-cut `δ(S)` of a vertex set `S` is the set of edges with exactly one end in `S`; it is
  odd if it has an odd number of edges. (`δ(∅) = ∅` is even, so no nondegeneracy condition on `S`
  is needed.)
-/

namespace OMA.S_opg_intersecting_two_perfect_matchings

/-- The edge-cut `δ(S)`: edges of `G` with exactly one end in `S`. -/
def edgeCut {V : Type} (G : SimpleGraph V) (S : Set V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∉ S}

/-- `F` contains an odd edge-cut. -/
def ContainsOddEdgeCut {V : Type} (G : SimpleGraph V) (F : Set (Sym2 V)) : Prop :=
  ∃ S : Set V, edgeCut G S ⊆ F ∧ Odd (edgeCut G S).ncard

/-- Every bridgeless cubic graph has two perfect matchings whose intersection contains no odd
edge-cut. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) →
    ∃ M₁ M₂ : G.Subgraph, M₁.IsPerfectMatching ∧ M₂.IsPerfectMatching ∧
      ¬ ContainsOddEdgeCut G (M₁.edgeSet ∩ M₂.edgeSet) := by
  sorry

end OMA.S_opg_intersecting_two_perfect_matchings
