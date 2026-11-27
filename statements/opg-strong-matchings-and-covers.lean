import Mathlib

/-!
# Strong matchings and covers

Source: https://www.openproblemgarden.org/op/strong_matchings_and_covers
Credit: @lzvxck

The source: let `H` be a hypergraph. A strongly maximal matching is a matching `F ⊆ E(H)`
so that `|F' \ F| ≤ |F \ F'|` for every matching `F'`. A strongly minimal cover is a (vertex)
cover `X ⊆ V(H)` so that `|X' \ X| ≥ |X \ X'|` for every cover `X'`.
Conjecture: if `H` is a (possibly infinite) hypergraph in which all edges have size `≤ k` for
some integer `k`, then `H` has a strongly maximal matching and a strongly minimal cover.

This file states that headline conjecture. (The page also records a second conjecture of
Aharoni, on hypergraphs of independent sets; it is not part of this statement.)

Conventions: a hypergraph is a vertex type `V` and an edge type `E` with each edge `e` given
by a nonempty finite vertex set `edge e` (so parallel edges are allowed), of size at most `k`.
A matching is a set of pairwise disjoint edges; a cover is a set of vertices meeting every
edge. Sizes `|·|` are cardinalities (`Cardinal.mk`), since the sets may be infinite.
-/

namespace OMA.S_opg_strong_matchings_and_covers

/-- `F` is a matching: its edges are pairwise disjoint. -/
def IsMatching {V E : Type*} (edge : E → Set V) (F : Set E) : Prop :=
  F.Pairwise fun e f => Disjoint (edge e) (edge f)

/-- `X` is a cover: it meets every edge. -/
def IsCover {V E : Type*} (edge : E → Set V) (X : Set V) : Prop :=
  ∀ e, (edge e ∩ X).Nonempty

/-- **Strong matchings and covers (Aharoni).** A hypergraph whose edges are nonempty and have
at most `k` vertices has a strongly maximal matching and a strongly minimal cover. -/
theorem main : ∀ (V E : Type) (edge : E → Set V) (k : ℕ),
    (∀ e, (edge e).Nonempty ∧ (edge e).Finite ∧ (edge e).ncard ≤ k) →
      (∃ F : Set E, IsMatching edge F ∧
        ∀ F' : Set E, IsMatching edge F' →
          Cardinal.mk ↥(F' \ F) ≤ Cardinal.mk ↥(F \ F')) ∧
      (∃ X : Set V, IsCover edge X ∧
        ∀ X' : Set V, IsCover edge X' →
          Cardinal.mk ↥(X \ X') ≤ Cardinal.mk ↥(X' \ X)) := by
  sorry

end OMA.S_opg_strong_matchings_and_covers
