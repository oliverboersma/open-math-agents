import Mathlib

/-!
# Splitting a digraph with minimum outdegree constraints

Source: https://www.openproblemgarden.org/op/splitting_a_digraph_with_minimum_outdegree_constraints
Credit: @LAPRAI

Problem (Alon): is there a minimum integer `f(d)` such that the vertices of any digraph with
minimum outdegree `f(d)` can be partitioned into two classes so that the minimum outdegree of
the subgraph induced by each class is at least `d`?

(Thomassen proved the case `d = 1`, with `f(1) = 3`.) A minimum exists as soon as some such
integer exists, so the question is whether, for every `d`, such an integer exists. We state the
positive answer.

## Encoding

* Digraphs are Mathlib `Digraph`s on a finite nonempty vertex type, without loops (no parallel
  arcs by construction). Minimum outdegree at least `f`: every vertex has at least `f`
  out-neighbours.
* A partition into two classes is a set `A` with `A` and its complement both nonempty. In the
  subgraph induced by `A`, the out-degree of `v ∈ A` is the number of out-neighbours of `v`
  lying in `A`; likewise for the complement.
-/

namespace OMA.S_opg_splitting_a_digraph_with_minimum_outdegree_constraints

/-- **Alon's problem**, positive answer: such an `f(d)` exists for every `d`. -/
theorem main : ∀ d : ℕ, ∃ f : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (D : Digraph V) [DecidableRel D.Adj],
    (∀ v, ¬ D.Adj v v) →
    (∀ v, f ≤ (Finset.univ.filter (fun w => D.Adj v w)).card) →
    ∃ A : Finset V, A.Nonempty ∧ Aᶜ.Nonempty ∧
      (∀ v ∈ A, d ≤ (A.filter (fun w => D.Adj v w)).card) ∧
      (∀ v ∈ Aᶜ, d ≤ (Aᶜ.filter (fun w => D.Adj v w)).card) := by
  sorry

end OMA.S_opg_splitting_a_digraph_with_minimum_outdegree_constraints
