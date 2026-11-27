import Mathlib

/-!
# Hamilton cycle in small d-diregular graphs

Source: https://www.openproblemgarden.org/op/hamilton_cycle_in_small_d_diregular_graphs
Credit: @LAPRAI

A directed graph is `k`-diregular if every vertex has indegree and outdegree at least `k`.
Conjecture (Jackson): for `d > 2`, every `d`-diregular oriented graph on at most `4d + 1`
vertices has a Hamilton cycle.

## Encoding

* An oriented graph is a finite Mathlib `Digraph V` with no pair of opposite arcs
  (`u → v` and `v → u`), hence in particular no loops.
* `d`-diregular is taken exactly as the source defines it: every indegree and every outdegree
  is at least `d`.
* A Hamilton cycle is a cyclic ordering of all the vertices along arcs: a bijection
  `c : Fin n ≃ V` with an arc from `c i` to `c (i + 1 mod n)` for every `i`. (A `d`-diregular
  oriented graph with `d > 2` and a vertex has at least `2d + 1 ≥ 7` vertices, so this is a
  genuine directed cycle.)
-/

namespace OMA.S_opg_hamilton_cycle_in_small_d_diregular_graphs

/-- An oriented graph: no two opposite arcs (so also no loops). -/
def IsOriented {V : Type} (G : Digraph V) : Prop :=
  ∀ u v, G.Adj u v → ¬ G.Adj v u

/-- The outdegree of `v`. -/
def outdegree {V : Type} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w)).card

/-- The indegree of `v`. -/
def indegree {V : Type} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj w v)).card

/-- `G` has a Hamilton cycle. -/
def HasHamiltonCycle {V : Type} [Fintype V] (G : Digraph V) : Prop :=
  ∃ c : Fin (Fintype.card V) ≃ V, ∀ i, G.Adj (c i) (c (finRotate _ i))

/-- **Jackson's conjecture on small diregular oriented graphs.** -/
theorem main : ∀ (V : Type) [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (d : ℕ), 2 < d →
    IsOriented G → (∀ v, d ≤ indegree G v ∧ d ≤ outdegree G v) →
    Fintype.card V ≤ 4 * d + 1 → HasHamiltonCycle G := by
  sorry

end OMA.S_opg_hamilton_cycle_in_small_d_diregular_graphs
