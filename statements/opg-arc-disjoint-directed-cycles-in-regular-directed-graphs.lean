import Mathlib

/-!
# Arc-disjoint directed cycles in regular directed graphs

Source: https://www.openproblemgarden.org/op/arc_disjoint_directed_cycles_in_regular_directed_graphs
Credit: @LAPRAI

Conjecture (Alon, McDiarmid, Molloy): if `G` is a `k`-regular directed graph with no parallel
arcs, then `G` contains a collection of `(k+1).choose 2` arc-disjoint directed cycles.
(Best possible, by the complete symmetric digraph on `k + 1` vertices.)

## Encoding

* `G` is a Mathlib `Digraph` on a finite nonempty vertex type: a relation has no parallel arcs
  by construction. Loops are excluded (`G` is irreflexive); opposite arcs `u → v`, `v → u` are
  allowed (they are present in the complete symmetric digraph).
* `k`-regular: every vertex has out-degree `k` and in-degree `k`.
* A directed cycle of length `m ≥ 2` is an injective sequence `c 0, …, c (m-1)` with an arc from
  each `c i` to `c (i + 1 mod m)`; its arc set is the set of these `m` arcs.
* The collection is a family of `(k+1).choose 2` directed cycles whose arc sets are pairwise
  disjoint.
-/

namespace OMA.S_opg_arc_disjoint_directed_cycles_in_regular_directed_graphs

/-- `c` is a directed cycle of `G` of length `m ≥ 2`. -/
def IsDirectedCycle {V : Type} (G : Digraph V) {m : ℕ} (c : Fin m → V) : Prop :=
  2 ≤ m ∧ Function.Injective c ∧ ∀ i : Fin m, G.Adj (c i) (c (finRotate m i))

/-- The set of arcs of the closed sequence `c`. -/
def arcSet {V : Type} {m : ℕ} (c : Fin m → V) : Set (V × V) :=
  Set.range (fun i : Fin m => (c i, c (finRotate m i)))

/-- **Alon–McDiarmid–Molloy conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : Digraph V)
    [DecidableRel G.Adj] (k : ℕ),
    (∀ v, ¬ G.Adj v v) →
    (∀ v, (Finset.univ.filter (fun w => G.Adj v w)).card = k) →
    (∀ v, (Finset.univ.filter (fun w => G.Adj w v)).card = k) →
    ∃ (len : Fin ((k + 1).choose 2) → ℕ) (cyc : ∀ j, Fin (len j) → V),
      (∀ j, IsDirectedCycle G (cyc j)) ∧
      ∀ i j, i ≠ j → Disjoint (arcSet (cyc i)) (arcSet (cyc j)) := by
  sorry

end OMA.S_opg_arc_disjoint_directed_cycles_in_regular_directed_graphs
