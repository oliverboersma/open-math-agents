import Mathlib

/-!
# Jaeger's modular orientation conjecture

Source: https://www.openproblemgarden.org/op/jaegers_modular_orientation_conjecture
Credit: @lzvxck

The source: every `4k`-edge-connected graph can be oriented so that
`indegree(v) - outdegree(v) ≡ 0 (mod 2k+1)` for every vertex `v`.

Graphs in flow theory may have parallel edges and loops, and edge-connectivity is sensitive to
parallel edges, so the statement is made for finite multigraphs: a finite vertex type `V`, a
finite edge type `E`, and for each edge `e` two ends `src e` and `tgt e`.

* An orientation chooses, for each edge, which end is the head: `o e = true` orients `e` from
  `src e` to `tgt e`, and `o e = false` from `tgt e` to `src e`. A loop adds one to both the
  indegree and the outdegree of its vertex.
* The multigraph is `n`-edge-connected if it stays connected after deleting any set of fewer
  than `n` edges.
* `k` is a positive integer (for `k = 1` this is Tutte's 3-flow conjecture).
-/

namespace OMA.S_opg_jaegers_modular_orientation_conjecture

/-- The simple graph recording which distinct vertices are joined by an edge outside `S`;
it is connected exactly when the multigraph minus the edges `S` is connected. -/
def underlying {V E : Type*} (src tgt : E → V) (S : Set E) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ e, e ∉ S ∧ src e = u ∧ tgt e = v

/-- The multigraph `(V, E, src, tgt)` is `n`-edge-connected: deleting any set of fewer than `n`
edges leaves it connected. -/
def IsEdgeConnected {V E : Type*} [Fintype E] (src tgt : E → V) (n : ℕ) : Prop :=
  ∀ S : Finset E, S.card < n → (underlying src tgt (S : Set E)).Connected

/-- The head of `e` under the orientation `o`. -/
def head {V E : Type*} (src tgt : E → V) (o : E → Bool) (e : E) : V :=
  if o e then tgt e else src e

/-- The tail of `e` under the orientation `o`. -/
def tail {V E : Type*} (src tgt : E → V) (o : E → Bool) (e : E) : V :=
  if o e then src e else tgt e

/-- **Jaeger's modular orientation conjecture.** For every positive integer `k`, every finite
`4k`-edge-connected multigraph has an orientation with
`indegree(v) - outdegree(v) ≡ 0 (mod 2k+1)` at every vertex. -/
theorem main : ∀ (k : ℕ), 1 ≤ k → ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E]
    (src tgt : E → V), IsEdgeConnected src tgt (4 * k) →
      ∃ o : E → Bool, ∀ v : V,
        ((Finset.univ.filter fun e => head src tgt o e = v).card : ℤ) -
            (Finset.univ.filter fun e => tail src tgt o e = v).card ≡ 0 [ZMOD (2 * k + 1)] := by
  sorry

end OMA.S_opg_jaegers_modular_orientation_conjecture
