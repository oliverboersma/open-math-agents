import Mathlib

/-!
# 5-flow conjecture

Source: https://www.openproblemgarden.org/op/5_flow_conjecture
Credit: @biondadave

Conjecture (Tutte): Every bridgeless graph has a nowhere-zero 5-flow.

Conventions (standard in flow theory, matching the source's references [T54], [Tt66]):
- A graph is a finite multigraph: loops and parallel edges are allowed (the source mentions
  loopless planar graphs, so loops are part of the setting). It is given by finite types `V`
  (vertices) and `E` (edges) with endpoint maps `tail head : E → V`, which also fix a reference
  orientation. Whether a nowhere-zero `k`-flow exists does not depend on that orientation:
  reversing an edge corresponds to negating its flow value.
- An edge `e` is a bridge if deleting it disconnects its two endpoints, that is, `tail e` and
  `head e` are not joined by a walk avoiding `e`. A loop is never a bridge. A graph is bridgeless
  if it has no bridge.
- A nowhere-zero `k`-flow is an integer edge labelling `f` with `0 < |f e| < k` for every edge
  and with flow conservation at every vertex: total inflow equals total outflow. (By Tutte this
  is equivalent to a nowhere-zero `ℤ/kℤ`-flow.)
-/

namespace OMA.S_opg_5_flow_conjecture

/-- `u` and `w` are joined by an edge other than `e` (in either direction). -/
def AdjWithout {V E : Type} (tail head : E → V) (e : E) (u w : V) : Prop :=
  ∃ e' : E, e' ≠ e ∧ ((tail e' = u ∧ head e' = w) ∨ (tail e' = w ∧ head e' = u))

/-- The multigraph has no bridge: the endpoints of every edge stay connected without it. -/
def Bridgeless {V E : Type} (tail head : E → V) : Prop :=
  ∀ e : E, Relation.ReflTransGen (AdjWithout tail head e) (tail e) (head e)

/-- `f` is a nowhere-zero `k`-flow for the oriented multigraph `(tail, head)`. -/
def IsNowhereZeroFlow {V E : Type} [Fintype E] [DecidableEq V] (tail head : E → V)
    (k : ℕ) (f : E → ℤ) : Prop :=
  (∀ e, 0 < |f e| ∧ |f e| < k) ∧
  ∀ v : V, (∑ e ∈ Finset.univ.filter (fun e => head e = v), f e) =
    ∑ e ∈ Finset.univ.filter (fun e => tail e = v), f e

theorem main :
    ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] (tail head : E → V),
      Bridgeless tail head → ∃ f : E → ℤ, IsNowhereZeroFlow tail head 5 f := by
  sorry

end OMA.S_opg_5_flow_conjecture
