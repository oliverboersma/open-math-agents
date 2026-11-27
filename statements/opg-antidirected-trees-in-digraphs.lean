import Mathlib

/-!
# Antidirected trees in digraphs

Source: https://www.openproblemgarden.org/op/antidirected_trees_in_digraphs
Credit: @LAPRAI

An antidirected tree is an orientation of a tree in which every vertex has either in-degree `0`
or out-degree `0`. Conjecture (Addario-Berry, Havet, Linhares Sales, Reed, Thomassé): let `D` be
a digraph. If `|A(D)| > (k - 2) |V(D)|`, then `D` contains every antidirected tree of order `k`.

## Encoding

* `D` is a Mathlib `Digraph` on a finite vertex type, loopless (no parallel arcs by
  construction; opposite arcs are allowed, as in symmetric digraphs). `|A(D)|` is the number
  of ordered pairs `(u, v)` with an arc `u → v`. The inequality is taken in `ℤ`.
* An oriented tree of order `k` is a `Digraph` `T` on `Fin k`, with no loops and no pair of
  opposite arcs, whose underlying undirected graph `SimpleGraph.fromRel T.Adj` is a tree.
  It is antidirected if every vertex has in-degree `0` or out-degree `0`.
* `D` contains `T` if there is an injective map `f : Fin k → V` sending each arc `a → b` of `T`
  to an arc `f a → f b` of `D`.
-/

namespace OMA.S_opg_antidirected_trees_in_digraphs

/-- `T` is an antidirected tree (on `Fin k`). -/
def IsAntidirectedTree {k : ℕ} (T : Digraph (Fin k)) : Prop :=
  (∀ a b, T.Adj a b → ¬ T.Adj b a) ∧ (SimpleGraph.fromRel T.Adj).IsTree ∧
    ∀ v, (∀ u, ¬ T.Adj u v) ∨ (∀ w, ¬ T.Adj v w)

/-- **Conjecture (Addario-Berry, Havet, Linhares Sales, Reed, Thomassé).** -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (k : ℕ),
    (∀ v, ¬ D.Adj v v) →
    ((k : ℤ) - 2) * (Fintype.card V : ℤ) <
      ((Finset.univ.filter (fun p : V × V => D.Adj p.1 p.2)).card : ℤ) →
    ∀ T : Digraph (Fin k), IsAntidirectedTree T →
      ∃ f : Fin k → V, Function.Injective f ∧ ∀ a b, T.Adj a b → D.Adj (f a) (f b) := by
  sorry

end OMA.S_opg_antidirected_trees_in_digraphs
