import Mathlib

/-!
# Seymour's self-minor conjecture

Source: https://www.openproblemgarden.org/op/seymours_self_minor_conjecture
Credit: @lzvxck

The source: every infinite graph is a proper minor of itself.

Scope: the statement is made for countably infinite graphs. Over all infinite graphs it is
false: Oporowski (A counterexample to Seymour's self-minor conjecture, J. Graph Theory 14
(1990) 521-524) built a graph of size continuum that is not a proper minor of itself. The
countable case is the open one (and the one that implies the graph minor theorem).

Conventions: graphs are simple. A minor of `G` isomorphic to `G`
is given by a model: for each vertex `v` a branch set `B v` of vertices of `G`, the branch sets
pairwise disjoint and each inducing a connected subgraph, such that adjacent `u, v` have an
edge of `G` between `B u` and `B v`. The minor is proper when at least one deletion or
contraction was made: some vertex of `G` lies in no branch set, or some branch set has two or
more vertices, or some edge of `G` joins `B u` and `B v` for distinct non-adjacent `u, v`.
(If none of these holds, every branch set is a single vertex, the branch map is a bijection of
`V`, and it is an isomorphism, so no deletion or contraction was made.)
-/

namespace OMA.S_opg_seymours_self_minor_conjecture

/-- `B` is a model of `G` as a minor of itself: disjoint connected branch sets, with an edge
between the branch sets of any two adjacent vertices. -/
def IsSelfMinorModel {V : Type*} (G : SimpleGraph V) (B : V → Set V) : Prop :=
  (∀ v, (G.induce (B v)).Connected) ∧
    (Pairwise fun u v => Disjoint (B u) (B v)) ∧
    ∀ u v, G.Adj u v → ∃ x ∈ B u, ∃ y ∈ B v, G.Adj x y

/-- The model `B` is proper: it deletes a vertex, contracts an edge, or deletes an edge. -/
def IsProperModel {V : Type*} (G : SimpleGraph V) (B : V → Set V) : Prop :=
  (∃ w, ∀ v, w ∉ B v) ∨ (∃ v, (B v).Nontrivial) ∨
    ∃ u v x y, u ≠ v ∧ ¬ G.Adj u v ∧ x ∈ B u ∧ y ∈ B v ∧ G.Adj x y

/-- **Seymour's self-minor conjecture (countable case).** Every countably infinite graph is a
proper minor of itself. -/
theorem main : ∀ (V : Type) [Countable V] [Infinite V] (G : SimpleGraph V),
    ∃ B : V → Set V, IsSelfMinorModel G B ∧ IsProperModel G B := by
  sorry

end OMA.S_opg_seymours_self_minor_conjecture
