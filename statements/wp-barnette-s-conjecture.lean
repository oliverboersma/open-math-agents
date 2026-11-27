import Mathlib

/-!
# Barnette's conjecture

Source: https://en.wikipedia.org/wiki/Barnette's_conjecture
Credit: @bcrowther86-eng

Barnette's conjecture (Barnette 1969): every cubic bipartite polyhedral graph is Hamiltonian,
that is, every cubic bipartite three-connected planar graph has a Hamiltonian cycle.

Conventions (as in the source and standard references such as Diestel's *Graph Theory*):
- Graphs are finite simple graphs, given as a `SimpleGraph` on a finite vertex type `V`.
- `G` is cubic if every vertex has exactly three neighbours.
- `G` is bipartite if its vertices can be 2-coloured so that every edge joins the two colours
  (Mathlib's `SimpleGraph.IsBipartite`).
- `G` is `k`-vertex-connected if it has more than `k` vertices and `G - X` is connected for
  every set `X` of fewer than `k` vertices; polyhedral means planar and 3-vertex-connected.
- A graph is planar if it has a plane drawing: distinct points of `ℝ²` for the vertices and,
  for every edge, an arc (a continuous injective image of `[0, 1]`) joining its endpoints,
  whose interior meets no vertex and no other edge's interior (same definition as the merged
  statement `statements/wp-apex-graph.lean`).
- `G` is Hamiltonian if it has a cycle passing through every vertex exactly once
  (Mathlib's `SimpleGraph.Walk.IsHamiltonianCycle`).
-/

namespace OMA.S_wp_barnette_s_conjecture

open SimpleGraph

/-- `G` is cubic: every vertex has exactly three neighbours. -/
def IsCubic {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ v : V, (G.neighborSet v).ncard = 3

/-- `G` is `k`-vertex-connected: more than `k` vertices, and deleting fewer than `k` vertices
leaves a connected graph. -/
def IsKVertexConnected {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ X : Finset V, X.card < k → (G.induce ((X : Set V)ᶜ)).Connected

/-- `G` has a plane drawing: vertices at distinct points, edges as arcs joining their endpoints,
with arc interiors avoiding all vertices and the interiors of all other arcs. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (pos : V → ℝ × ℝ) (arc : G.edgeSet → C(unitInterval, ℝ × ℝ)),
    Function.Injective pos ∧
    (∀ e, Function.Injective (arc e)) ∧
    (∀ e, Sym2.map pos e.1 = s(arc e 0, arc e 1)) ∧
    (∀ e (t : unitInterval), (t : ℝ) ∈ Set.Ioo 0 1 → ∀ v, arc e t ≠ pos v) ∧
    (∀ e f, e ≠ f → ∀ s t : unitInterval, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      arc e s ≠ arc f t)

theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsCubic G → G.IsBipartite → IsKVertexConnected G 3 → IsPlanar G →
        ∃ (a : V) (p : G.Walk a a), p.IsHamiltonianCycle := by
  sorry

end OMA.S_wp_barnette_s_conjecture
