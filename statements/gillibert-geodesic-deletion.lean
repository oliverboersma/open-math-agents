import Mathlib

/-!
# Geodesic deletion conjecture (vertex-transitive graphs)

Source: https://github.com/Gillibert/ConjecturesGillibert/blob/main/geodesic_deletion_conjecture.tex
Credit: @Gillibert

Let `G` be a finite connected vertex-transitive graph with at least three vertices.
For every geodesic `P` of `G`, the induced subgraph `G - V(P)` is connected.

Translation notes:
* A geodesic is a walk `p : G.Walk u v` that is a path and has length `G.dist u v`.
  The source does not exclude the one-vertex geodesic (`u = v`), so it is included. This does
  not change the conjecture: a connected vertex-transitive graph on at least 3 vertices has
  vertex connectivity at least 2 (Watkins 1970: at least 2(d+1)/3 for degree d ≥ 2), so deleting
  a single vertex never disconnects it.
* `G - V(P)` is `G.induce {x | x ∉ p.support}`: every vertex of `P`, endpoints included,
  is deleted.
* Mathlib's `Connected` requires a nonempty vertex type. Under the hypotheses the remaining
  set is never empty: a geodesic through all `n` vertices forces `G` to be the path on `n`
  vertices, which is not vertex-transitive for `n ≥ 3`.
* `IsVertexTransitive` is the same definition as `LovaszConjecture.IsVertexTransitive`
  in formal-conjectures.
-/

namespace OMA.S_gillibert_geodesic_deletion

open SimpleGraph

/-- A graph is vertex-transitive if any vertex can be mapped to any other by an automorphism. -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

theorem main :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 3 ≤ Fintype.card V →
      ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
        (G.induce {x | x ∉ p.support}).Connected := by
  sorry

end OMA.S_gillibert_geodesic_deletion
