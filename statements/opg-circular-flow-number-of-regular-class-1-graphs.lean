import Mathlib

/-!
# Circular flow number of regular class 1 graphs

Source: https://www.openproblemgarden.org/op/circular_flow_number_of_regular_class_1_graphs
Credit: @lzvxck

The source: a nowhere-zero `r`-flow `(D(G), φ)` on `G` is an orientation `D` of `G` together
with a function `φ` from the edge set of `G` into the real numbers such that
`1 ≤ |φ(e)| ≤ r - 1` for all `e`, and the flow into each vertex equals the flow out of it.
The circular flow number of `G` is `F_c(G) = inf {r | G has a nowhere-zero r-flow}`. A graph
with maximum vertex degree `k` is a class 1 graph if its edge chromatic number is `k`.
Conjecture: let `t ≥ 1` be an integer and `G` a `(2t+1)`-regular graph. If `G` is a class 1
graph, then `F_c(G) ≤ 2 + 2/t`.

Conventions: graphs are finite loopless multigraphs (parallel edges allowed): a finite vertex
type `V`, a finite edge type `E`, and for each edge `e` two distinct ends `src e`, `tgt e`.
Reversing an edge negates its flow value, so the orientation `D` is fixed as `src → tgt`
without loss of generality. The degree of `v` is the number of edges with an end at `v`.
The circular flow number `F_c(G)` is the infimum of the real numbers `r` for which `G` has a
nowhere-zero `r`-flow. Class 1 for a `(2t+1)`-regular graph means a proper edge colouring
with `2t+1` colours (edges sharing an end get different colours); such a graph is bridgeless,
so the set of `r` is nonempty.
-/

namespace OMA.S_opg_circular_flow_number_of_regular_class_1_graphs

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

/-- **Circular flow number of regular class 1 graphs (Steffen).** For an integer `t ≥ 1`,
every `(2t+1)`-regular class 1 graph has circular flow number at most `2 + 2/t`. -/
theorem main : ∀ (t : ℕ), 1 ≤ t → ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E]
    (src tgt : E → V), (∀ e, src e ≠ tgt e) →
      (∀ v : V, (Finset.univ.filter fun e => src e = v).card +
        (Finset.univ.filter fun e => tgt e = v).card = 2 * t + 1) →
      (∃ c : E → Fin (2 * t + 1), ∀ e f, e ≠ f →
        (src e = src f ∨ src e = tgt f ∨ tgt e = src f ∨ tgt e = tgt f) → c e ≠ c f) →
      circularFlowNumber src tgt ≤ 2 + 2 / (t : ℝ) := by
  sorry

end OMA.S_opg_circular_flow_number_of_regular_class_1_graphs
