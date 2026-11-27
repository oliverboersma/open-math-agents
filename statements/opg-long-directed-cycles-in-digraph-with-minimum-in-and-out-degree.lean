import Mathlib

/-!
# Long directed cycles in diregular digraphs

Source: https://www.openproblemgarden.org/op/long_directed_cycles_in_digraph_with_minimum_in_and_out_degree
Credit: @LAPRAI

*Reference:* B. Jackson, Long paths and cycles in oriented graphs, J. Graph Theory 5 (1981),
145–157.

Conjecture (Jackson): every strong oriented graph in which each vertex has indegree and outdegree
at least `d` contains a directed cycle of length at least `2d + 1`.

## Encoding

* An oriented graph is a finite Mathlib `Digraph V` with no pair of opposite arcs
  (`u → v` and `v → u`), hence in particular no loops.
* *Strong* (strongly connected): every vertex reaches every other vertex by a directed walk.
* `d ≥ 1` and a nonempty vertex set: for `d = 0` a single vertex is a strong oriented graph with
  no cycle, and the empty graph satisfies every hypothesis vacuously, so the source's statement
  is about positive `d` and graphs with vertices.
* A directed cycle of length `k` is an injective sequence `c 0, …, c (k-1)` of vertices with an
  arc from each `c i` to `c (i + 1 mod k)`.
-/

namespace OMA.S_opg_long_directed_cycles_in_digraph_with_minimum_in_and_out_degree

/-- An oriented graph: no two opposite arcs (so also no loops). -/
def IsOriented {V : Type} (G : Digraph V) : Prop :=
  ∀ u v, G.Adj u v → ¬ G.Adj v u

/-- A strongly connected digraph: every vertex reaches every vertex along arcs. -/
def IsStrong {V : Type} (G : Digraph V) : Prop :=
  ∀ u v, Relation.ReflTransGen G.Adj u v

/-- The outdegree of `v`. -/
def outdegree {V : Type} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w)).card

/-- The indegree of `v`. -/
def indegree {V : Type} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj w v)).card

/-- `G` has a directed cycle of length exactly `k`. -/
def HasDirectedCycleOfLength {V : Type} (G : Digraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → V, Function.Injective c ∧ ∀ i : Fin k, G.Adj (c i) (c (finRotate k i))

/-- **Jackson's conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (d : ℕ), 1 ≤ d → IsOriented G → IsStrong G →
    (∀ v, d ≤ indegree G v ∧ d ≤ outdegree G v) →
    ∃ k, 2 * d + 1 ≤ k ∧ HasDirectedCycleOfLength G k := by
  sorry

end OMA.S_opg_long_directed_cycles_in_digraph_with_minimum_in_and_out_degree
