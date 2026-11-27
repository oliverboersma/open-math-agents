import Mathlib

/-!
# Apex graph

Source: https://en.wikipedia.org/wiki/apex_graph
Credit: @sntntHb

Jørgensen's conjecture: every 6-vertex-connected `K₆`-minor-free graph is an apex graph.

Conventions (standard, as in Diestel's *Graph Theory* and the source):
- Graphs are finite simple graphs, given as a `SimpleGraph` on a finite vertex type `V`.
- `G` is `k`-vertex-connected if it has more than `k` vertices and `G - X` is connected for
  every set `X` of fewer than `k` vertices.
- `H` is a minor of `G` if there are pairwise disjoint, nonempty vertex sets `B w ⊆ V(G)`
  (one per vertex `w` of `H`), each inducing a connected subgraph of `G`, such that whenever
  `w w'` is an edge of `H` some vertex of `B w` is adjacent in `G` to some vertex of `B w'`.
- A graph is planar if it has a plane drawing: distinct points of `ℝ²` for the vertices and,
  for every edge, an arc (a continuous injective image of `[0, 1]`) joining its endpoints,
  whose interior meets no vertex and no other edge's interior.
- `G` is an apex graph if deleting a single vertex leaves a planar graph.
-/

namespace OMA.S_wp_apex_graph

open SimpleGraph

/-- `G` is `k`-vertex-connected: more than `k` vertices, and deleting fewer than `k` vertices
leaves a connected graph. -/
def IsKVertexConnected {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ X : Finset V, X.card < k → (G.induce ((X : Set V)ᶜ)).Connected

/-- `H` is a minor of `G`, witnessed by branch sets `B w`. -/
def IsMinor {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ B : W → Set V,
    (∀ w, (B w).Nonempty) ∧
    (∀ w w', w ≠ w' → Disjoint (B w) (B w')) ∧
    (∀ w, (G.induce (B w)).Connected) ∧
    (∀ w w', H.Adj w w' → ∃ x ∈ B w, ∃ y ∈ B w', G.Adj x y)

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

/-- `G` is an apex graph: deleting some single vertex leaves a planar graph. -/
def IsApex {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ v : V, IsPlanar (G.induce ({v}ᶜ : Set V))

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      IsKVertexConnected G 6 → ¬ IsMinor (⊤ : SimpleGraph (Fin 6)) G → IsApex G := by
  sorry

end OMA.S_wp_apex_graph
