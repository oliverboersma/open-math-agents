import Mathlib

/-!
# Number of cliques in minor-closed classes

Source: https://www.openproblemgarden.org/op/number_of_cliques_in_minor_closed_classes
Credit: @lzvxck

The source: is there a constant `c` such that every `n`-vertex `K_t`-minor-free graph has at
most `c^t n` cliques? Here a clique is a (not necessarily maximal) set of pairwise adjacent
vertices in a graph.

The affirmative answer is stated (the source records that Lee and Oum answered the question
in the affirmative; it then asks for the minimum constant, which is not part of this
statement). Conventions: graphs are finite and simple; `n = |V(G)|`; cliques are counted as
nonempty vertex sets, by size: the number of cliques is `∑_{k=1}^{n}` of the number of
`k`-cliques (Mathlib's `cliqueFinset k`). The empty set is left out (otherwise the empty graph,
with `n = 0`, would have one clique and no bound of the form `c^t n` could hold).
`G` is `K_t`-minor-free when there are no `t` pairwise disjoint vertex sets, each inducing a
connected subgraph, with an edge of `G` between any two.
-/

namespace OMA.S_opg_number_of_cliques_in_minor_closed_classes

/-- `G` has a `K_t`-minor: `t` pairwise disjoint connected branch sets, any two joined by an
edge of `G`. -/
def HasCompleteMinor {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V, (∀ i, (G.induce (B i)).Connected) ∧
    (Pairwise fun i j => Disjoint (B i) (B j)) ∧
    ∀ i j, i ≠ j → ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y

/-- **Number of cliques in `K_t`-minor-free graphs (Wood).** There is a constant `c` such that
every `n`-vertex `K_t`-minor-free graph has at most `c^t n` cliques. -/
theorem main : ∃ c : ℝ, ∀ (t : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], ¬ HasCompleteMinor G t →
      ((∑ k ∈ Finset.Icc 1 (Fintype.card V), (G.cliqueFinset k).card : ℕ) : ℝ) ≤
        c ^ t * Fintype.card V := by
  sorry

end OMA.S_opg_number_of_cliques_in_minor_closed_classes
