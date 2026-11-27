import Mathlib

/-!
# Equal halves conjecture (vertex-transitive graphs)

Source: https://github.com/Gillibert/ConjecturesGillibert/blob/main/equal_halves_conjecture.tex
Credit: @Gillibert

Every finite connected vertex-transitive graph `G` of even order admits a partition
`V(G) = A ⊔ B` into two nonempty sets such that `G[A]` and `G[B]` are connected and isomorphic.

Translation notes:
* The partition is `A` and its complement `Aᶜ`; `G[A]` is `G.induce A`.
* Nonemptiness of both parts is stated explicitly, as in the source
  (it also follows from Mathlib's `Connected`, which requires a nonempty vertex type).
* Even order excludes the empty graph, since `G.Connected` already forces at least one vertex.
* The source proves the Cayley-graph case; the conjecture itself is stated here in full.
* `IsVertexTransitive` is the same definition as `LovaszConjecture.IsVertexTransitive`
  in formal-conjectures.
-/

namespace OMA.S_gillibert_equal_halves

open SimpleGraph

/-- A graph is vertex-transitive if any vertex can be mapped to any other by an automorphism. -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

theorem main :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → Even (Fintype.card V) →
      ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
        (G.induce A).Connected ∧ (G.induce Aᶜ).Connected ∧
        Nonempty (G.induce A ≃g G.induce Aᶜ) := by
  sorry

end OMA.S_gillibert_equal_halves
