import Mathlib

/-!
# Oriented trees in n-chromatic digraphs

Source: https://www.openproblemgarden.org/op/oriented_trees_in_n_chromatic_digraphs
Credit: @LAPRAI

Conjecture (Burr): every digraph with chromatic number at least `2k - 2` contains every oriented
tree of order `k` as a subdigraph.

## Encoding

* Digraphs are finite Mathlib `Digraph`s; the chromatic number of a digraph is that of its
  underlying undirected graph (`SimpleGraph.fromRel D.Adj`, which forgets loops and directions).
* An oriented tree of order `k` is a `Digraph (Fin k)` with no loops and no pair of opposite arcs
  whose underlying undirected graph is a tree.
* `D` contains `T` as a subdigraph if there is an injective map `f` from the vertices of `T` to
  those of `D` sending every arc `a → b` of `T` to an arc `f a → f b` of `D`.
* `k ≥ 2`: for `k = 1` the bound `2k - 2 = 0` would include the empty digraph, which contains no
  vertex; the source's bound is meant for nontrivial trees.
-/

namespace OMA.S_opg_oriented_trees_in_n_chromatic_digraphs

/-- `T` is an oriented tree: no loops, no opposite arcs, and its underlying graph is a tree. -/
def IsOrientedTree {W : Type} (T : Digraph W) : Prop :=
  (∀ a b, T.Adj a b → ¬ T.Adj b a) ∧ (SimpleGraph.fromRel T.Adj).IsTree

/-- `D` contains `T` as a subdigraph. -/
def ContainsSubdigraph {V W : Type} (D : Digraph V) (T : Digraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ a b, T.Adj a b → D.Adj (f a) (f b)

/-- **Burr's conjecture.** -/
theorem main : ∀ (k : ℕ), 2 ≤ k → ∀ (V : Type) [Fintype V] (D : Digraph V),
    ((2 * k - 2 : ℕ) : ℕ∞) ≤ (SimpleGraph.fromRel D.Adj).chromaticNumber →
    ∀ T : Digraph (Fin k), IsOrientedTree T → ContainsSubdigraph D T := by
  sorry

end OMA.S_opg_oriented_trees_in_n_chromatic_digraphs
