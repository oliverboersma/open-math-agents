import Mathlib

/-!
# 3-flow conjecture

Source: https://www.openproblemgarden.org/op/3_flow_conjecture
Credit: @biondadave

Conjecture (Tutte): Every 4-edge-connected graph has a nowhere-zero 3-flow.

This file states the main conjecture only. The source page also lists Jaeger's weak 3-flow
conjecture as open, but it has since been proved (Thomassen 2012 for 8-edge-connected graphs;
Lovász, Thomassen, Wu and Zhang 2013 for 6-edge-connected graphs), so it is not stated here.

Conventions (standard in flow theory):
- A graph is a finite multigraph: loops and parallel edges are allowed. It is given by finite
  types `V` (vertices) and `E` (edges) with endpoint maps `tail head : E → V`, which also fix a
  reference orientation. Whether a nowhere-zero `k`-flow exists does not depend on that
  orientation: reversing an edge corresponds to negating its flow value.
- A graph is `k`-edge-connected if it stays connected after deleting any set of fewer than `k`
  edges. Taking the empty set shows that such a graph is connected.
- A nowhere-zero `k`-flow is an integer edge labelling `f` with `0 < |f e| < k` for every edge
  and with flow conservation at every vertex: total inflow equals total outflow.
-/

namespace OMA.S_opg_3_flow_conjecture

/-- `u` and `w` are joined by an edge outside `S` (in either direction). -/
def AdjAvoiding {V E : Type} (tail head : E → V) (S : Finset E) (u w : V) : Prop :=
  ∃ e : E, e ∉ S ∧ ((tail e = u ∧ head e = w) ∨ (tail e = w ∧ head e = u))

/-- The multigraph is `k`-edge-connected: deleting fewer than `k` edges leaves it connected. -/
def EdgeConnected {V E : Type} (tail head : E → V) (k : ℕ) : Prop :=
  ∀ S : Finset E, S.card < k → ∀ u w : V, Relation.ReflTransGen (AdjAvoiding tail head S) u w

/-- `f` is a nowhere-zero `k`-flow for the oriented multigraph `(tail, head)`. -/
def IsNowhereZeroFlow {V E : Type} [Fintype E] [DecidableEq V] (tail head : E → V)
    (k : ℕ) (f : E → ℤ) : Prop :=
  (∀ e, 0 < |f e| ∧ |f e| < k) ∧
  ∀ v : V, (∑ e ∈ Finset.univ.filter (fun e => head e = v), f e) =
    ∑ e ∈ Finset.univ.filter (fun e => tail e = v), f e

theorem main :
    ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] (tail head : E → V),
      EdgeConnected tail head 4 → ∃ f : E → ℤ, IsNowhereZeroFlow tail head 3 f := by
  sorry

end OMA.S_opg_3_flow_conjecture
