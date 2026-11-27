import Mathlib

/-!
# 3-Edge-Coloring Conjecture

Source: https://www.openproblemgarden.org/op/3_edge_coloring_conjecture
Credit: @lzvxck

The source states the conjecture and then its reformulation via 4-flows:
"Suppose `G` is a cubic graph with a nowhere-zero 4-flow, then there is an edge `e ∈ E(G)` such
that `G - e` has a nowhere-zero 4-flow." This file states that 4-flow form. (By Tutte, a cubic
graph has a nowhere-zero 4-flow iff it is 3-edge-colourable, and `G - e` has a nowhere-zero
4-flow iff the cubic graph homeomorphic to it does, which gives the first form.) The
hypotheses of the first form, `G` connected with `|V(G)| > 2`, are kept: without them the
empty graph would be a trivial counterexample (it has a 4-flow but no edge).

Conventions: graphs are finite multigraphs (parallel edges and loops allowed, as is usual in
flow theory): a finite vertex type `V`, a finite edge type `E`, and for each edge `e` a tail
`src e` and a head `tgt e` (a reference orientation; reversing an edge negates its flow value,
so the choice is immaterial). Cubic means every vertex has degree 3, a loop counting twice.
A nowhere-zero 4-flow is `f : E → ℤ` with `0 < |f e| < 4` on every edge and, at every vertex,
total inflow equal to total outflow. A nowhere-zero 4-flow of `G - e` is the same as
`f : E → ℤ` with `f e = 0`, `0 < |f d| < 4` for every other edge `d`, and conservation at
every vertex.
-/

namespace OMA.S_opg_3_edge_coloring_conjecture

/-- The simple graph recording which distinct vertices are joined by an edge; it is connected
exactly when the multigraph is connected. -/
def underlying {V E : Type*} (src tgt : E → V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ e, src e = u ∧ tgt e = v

/-- Conservation of `f` at every vertex of the multigraph `(V, E, src, tgt)`. -/
def IsConservative {V E : Type*} [Fintype E] [DecidableEq V] (src tgt : E → V)
    (f : E → ℤ) : Prop :=
  ∀ v, ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), f e =
    ∑ e ∈ Finset.univ.filter (fun e => src e = v), f e

/-- **3-edge-coloring conjecture (4-flow form).** If a finite connected cubic multigraph with
more than two vertices has a nowhere-zero 4-flow, then for some edge `e`, `G - e` has a
nowhere-zero 4-flow. -/
theorem main : ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (src tgt : E → V),
    (underlying src tgt).Connected → 2 < Fintype.card V →
    (∀ v : V, (Finset.univ.filter fun e => src e = v).card +
      (Finset.univ.filter fun e => tgt e = v).card = 3) →
    (∃ f : E → ℤ, (∀ d, 0 < |f d| ∧ |f d| < 4) ∧ IsConservative src tgt f) →
      ∃ e : E, ∃ f : E → ℤ, f e = 0 ∧ (∀ d, d ≠ e → 0 < |f d| ∧ |f d| < 4) ∧
        IsConservative src tgt f := by
  sorry

end OMA.S_opg_3_edge_coloring_conjecture
