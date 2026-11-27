import Mathlib

/-!
# Graphs with a forbidden induced tree are chi-bounded (Gyárfás' conjecture)

Source: https://www.openproblemgarden.org/op/graphs_with_a_forbidden_induced_tree_are_chi_bounded

Say that a family F of graphs is χ-bounded if there exists a function f : ℕ → ℕ so that
every G ∈ F satisfies χ(G) ≤ f(ω(G)).

Conjecture (Gyárfás). For every fixed tree T, the family of graphs with no induced
subgraph isomorphic to T is χ-bounded.

Conventions:
* Graphs are finite simple graphs (`SimpleGraph V` with `Fintype V`), the standard
  setting of χ-boundedness; the tree T is a finite simple graph with `T.IsTree`
  (connected and acyclic, hence with at least one vertex).
* G has an induced subgraph isomorphic to T  is Mathlib's `T.IsIndContained G`, i.e. there
  is an induced embedding `T ↪g G` (an injective map preserving adjacency and
  non-adjacency).
* χ(G) is `G.chromaticNumber : ℕ∞` (finite for finite graphs) and ω(G) is
  `G.cliqueNum : ℕ`, the largest size of a clique (a genuine maximum for finite graphs).
* f : ℕ → ℕ depends only on T, exactly as in the definition of χ-bounded on the page.
-/

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

namespace OMA.S_opg_graphs_with_a_forbidden_induced_tree_are_chi_bounded

theorem main :
    ∀ (W : Type) [Fintype W] (T : SimpleGraph W), T.IsTree →
      ∃ f : ℕ → ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
        ¬ T.IsIndContained G → G.chromaticNumber ≤ (f G.cliqueNum : ℕ∞) := by
  sorry

end OMA.S_opg_graphs_with_a_forbidden_induced_tree_are_chi_bounded
