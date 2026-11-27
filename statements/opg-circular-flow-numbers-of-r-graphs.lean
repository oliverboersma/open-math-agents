import Mathlib

/-!
# Circular flow numbers of r-graphs

Source: https://www.openproblemgarden.org/op/circular_flow_numbers_of_r_graphs
Credit: @lzvxck

The source: a nowhere-zero `r`-flow `(D(G), φ)` on `G` is an orientation `D` of `G` together
with a function `φ` from the edge set of `G` into the real numbers such that
`1 ≤ |φ(e)| ≤ r - 1` for all `e`, and the flow into each vertex equals the flow out of it.
A `(2t+1)`-regular graph `G` is a `(2t+1)`-graph if `|∂_G(X)| ≥ 2t+1` for every `X ⊆ V(G)`
with `|X|` odd. Conjecture: let `t > 1` be an integer. If `G` is a `(2t+1)`-graph, then
`F_c(G) ≤ 2 + 2/t`.

Conventions: graphs are finite loopless multigraphs (parallel edges allowed): a finite vertex
type `V`, a finite edge type `E`, and for each edge `e` two distinct ends `src e`, `tgt e`.
Reversing an edge negates its flow value, so the orientation `D` is fixed as `src → tgt`
without loss of generality. The degree of `v` is the number of edges with an end at `v`, and
`∂_G(X)` is the set of edges with exactly one end in `X`. The circular flow number `F_c(G)`
is the infimum of the real numbers `r` for which `G` has a nowhere-zero `r`-flow (a
`(2t+1)`-graph is bridgeless, so this set is nonempty; for finite graphs the infimum is
known to be attained).
-/

namespace OMA.S_opg_circular_flow_numbers_of_r_graphs

/-- `φ` is a nowhere-zero real `r`-flow on the multigraph `(V, E, src, tgt)`, oriented
`src → tgt`. -/
def IsNowhereZeroRealFlow {V E : Type*} [Fintype E] [DecidableEq V] (src tgt : E → V) (r : ℝ)
    (φ : E → ℝ) : Prop :=
  (∀ e, 1 ≤ |φ e| ∧ |φ e| ≤ r - 1) ∧
  ∀ v, ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), φ e =
    ∑ e ∈ Finset.univ.filter (fun e => src e = v), φ e

/-- The circular flow number: the infimum of `r` such that a nowhere-zero `r`-flow exists. -/
noncomputable def circularFlowNumber {V E : Type*} [Fintype E] [DecidableEq V]
    (src tgt : E → V) : ℝ :=
  sInf {r : ℝ | ∃ φ : E → ℝ, IsNowhereZeroRealFlow src tgt r φ}

/-- **Circular flow numbers of `r`-graphs (Steffen).** For an integer `t > 1`, every
`(2t+1)`-graph has circular flow number at most `2 + 2/t`. -/
theorem main : ∀ (t : ℕ), 1 < t → ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E]
    (src tgt : E → V), (∀ e, src e ≠ tgt e) →
      (∀ v : V, (Finset.univ.filter fun e => src e = v).card +
        (Finset.univ.filter fun e => tgt e = v).card = 2 * t + 1) →
      (∀ X : Finset V, Odd X.card →
        2 * t + 1 ≤ (Finset.univ.filter fun e =>
          (src e ∈ X ∧ tgt e ∉ X) ∨ (tgt e ∈ X ∧ src e ∉ X)).card) →
      circularFlowNumber src tgt ≤ 2 + 2 / (t : ℝ) := by
  sorry

end OMA.S_opg_circular_flow_numbers_of_r_graphs
