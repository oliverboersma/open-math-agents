import Mathlib

/-!
# Cycle double covers containing predefined 2-regular subgraphs

Source: https://www.openproblemgarden.org/op/cycle_double_covers_containing_predefined_2_regular_subgraphs
Credit: @lzvxck

The source: let `G` be a 2-connected cubic graph and let `S` be a 2-regular subgraph such that
`G - E(S)` is connected. Then `G` has a cycle double cover which contains `S` (i.e. all cycles
of `S`). A "cycle" is a connected 2-regular subgraph, and a "cycle double cover" of `G` is a
set of cycles of `G` such that every edge of `G` is contained in precisely two cycles of the
set.

Conventions: graphs are finite and simple. `G` is 2-connected when it has more than 2 vertices
and stays connected after deleting any single vertex. A subgraph is 2-regular when each of its
vertices has exactly two neighbours in it. `G - E(S)` is `G` with the edges of `S` deleted
(all vertices kept). "Contains all cycles of `S`" is stated as: every cycle of `G` that is a
subgraph of `S` belongs to the cover (in a 2-regular graph these are exactly its components).
-/

namespace OMA.S_opg_cycle_double_covers_containing_predefined_2_regular_subgraphs

/-- `G` is `k`-connected: more than `k` vertices, and deleting fewer than `k` vertices leaves
a connected graph. -/
def IsKConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

/-- The subgraph `H` is 2-regular: each of its vertices has exactly two neighbours in `H`. -/
def IsTwoRegular {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) : Prop :=
  ∀ v ∈ H.verts, (H.neighborSet v).ncard = 2

/-- `C` is a cycle of `G`: a connected 2-regular subgraph. -/
def IsCycleSubgraph {V : Type*} {G : SimpleGraph V} (C : G.Subgraph) : Prop :=
  C.Connected ∧ IsTwoRegular C

/-- **Cycle double covers containing a predefined 2-regular subgraph.** In a finite
2-connected cubic graph `G`, for every 2-regular subgraph `S` with `G - E(S)` connected, there
is a set of cycles of `G` covering every edge exactly twice and containing every cycle of
`S`. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsKConnected G 2 → G.IsRegularOfDegree 3 →
      ∀ S : G.Subgraph, IsTwoRegular S → (G.deleteEdges S.edgeSet).Connected →
        ∃ 𝒞 : Set G.Subgraph, (∀ C ∈ 𝒞, IsCycleSubgraph C) ∧
          (∀ e ∈ G.edgeSet, {C ∈ 𝒞 | e ∈ C.edgeSet}.ncard = 2) ∧
          ∀ C : G.Subgraph, C ≤ S → IsCycleSubgraph C → C ∈ 𝒞 := by
  sorry

end OMA.S_opg_cycle_double_covers_containing_predefined_2_regular_subgraphs
