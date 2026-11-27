import Mathlib

/-!
# Good Edge Labelings

Source: https://www.openproblemgarden.org/op/good_edge_labelings
Credit: @lzvxck

The source: a good edge labeling of a finite simple graph `G` is an assignment of distinct
numbers to the edges such that every cycle has at least two local maxima; equivalently, for
every pair of distinct vertices `u, v` there is at most one increasing path from `u` to `v`.
A graph is good-edge-labeling critical if it has no good edge labeling, but every proper
subgraph has a good edge labeling.
Conjecture: for every `c < 4`, there is only a finite number of good-edge-labeling critical
graphs with average degree less than `c`.

This file states the conjecture (not the open question on maximum edge density that precedes
it). Conventions:
* Labels are real numbers, given by `ℓ : Sym2 V → ℝ`, injective on the edges of `G`.
  The second (increasing path) form of the definition is used: a path is increasing when the
  labels of its edges, in order, are strictly increasing.
* Proper subgraphs may delete vertices as well as edges, so they are the subgraphs `H` of `G`
  (Mathlib's `G.Subgraph`) other than `G` itself, viewed as graphs on their own vertex set.
* The average degree of `G` is `2 |E(G)| / |V(G)|`.
* "Only a finite number of graphs" means finitely many up to isomorphism, which for finite
  graphs is the same as a bound `N` on their number of vertices.
-/

namespace OMA.S_opg_good_edge_labelings

/-- `ℓ` is a good edge labeling of `G`: distinct labels on edges, and for distinct `u, v` at
most one path from `u` to `v` whose edge labels strictly increase. -/
def IsGoodEdgeLabeling {W : Type*} (G : SimpleGraph W) (ℓ : Sym2 W → ℝ) : Prop :=
  Set.InjOn ℓ G.edgeSet ∧
    ∀ u v : W, u ≠ v → ∀ p q : G.Walk u v, p.IsPath → q.IsPath →
      (p.edges.map ℓ).IsChain (· < ·) → (q.edges.map ℓ).IsChain (· < ·) → p = q

/-- `G` has a good edge labeling. -/
def HasGoodEdgeLabeling {W : Type*} (G : SimpleGraph W) : Prop :=
  ∃ ℓ : Sym2 W → ℝ, IsGoodEdgeLabeling G ℓ

/-- `G` is good-edge-labeling critical: no good edge labeling, but every proper subgraph has
one. -/
def IsGELCritical {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ HasGoodEdgeLabeling G ∧ ∀ H : G.Subgraph, H ≠ ⊤ → HasGoodEdgeLabeling H.coe

/-- **Good edge labelings (Araújo, Cohen, Giroire, Havet).** For every `c < 4`, the
good-edge-labeling critical finite graphs of average degree less than `c` have a bounded number
of vertices (so there are finitely many of them up to isomorphism). -/
theorem main : ∀ c : ℝ, c < 4 → ∃ N : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    IsGELCritical G → 2 * (G.edgeSet.ncard : ℝ) / Fintype.card V < c →
      Fintype.card V ≤ N := by
  sorry

end OMA.S_opg_good_edge_labelings
