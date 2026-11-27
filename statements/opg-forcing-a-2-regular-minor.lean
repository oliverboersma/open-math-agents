import Mathlib

/-!
# Forcing a 2-regular minor

Source: https://www.openproblemgarden.org/op/forcing_a_2_regular_minor
Credit: @lzvxck

The source: every graph with average degree at least `(4/3) t - 2` contains every 2-regular
graph on `t` vertices as a minor.

Conventions: graphs are finite, simple and nonempty (so that the average degree
`2 |E(G)| / |V(G)|` is defined). A 2-regular graph on `t` vertices is a simple graph `H` on
`Fin t` in which every vertex has degree 2. `H` is a minor of `G` when there are pairwise
disjoint vertex sets `B i ⊆ V(G)` (branch sets), one for each vertex `i` of `H`, each inducing
a connected subgraph of `G`, with an edge of `G` between `B i` and `B j` whenever `i` and `j`
are adjacent in `H`.
-/

namespace OMA.S_opg_forcing_a_2_regular_minor

/-- `H` is a minor of `G`, given by a model with disjoint connected branch sets. -/
def IsMinor {V W : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ B : W → Set V, (∀ i, (G.induce (B i)).Connected) ∧
    (Pairwise fun i j => Disjoint (B i) (B j)) ∧
    ∀ i j, H.Adj i j → ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y

/-- **Forcing a 2-regular minor (Reed–Wood).** A nonempty finite graph with average degree at
least `(4/3) t - 2` contains every 2-regular graph on `t` vertices as a minor. -/
theorem main : ∀ (t : ℕ) (H : SimpleGraph (Fin t)) [DecidableRel H.Adj],
    H.IsRegularOfDegree 2 →
      ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (4 / 3 : ℝ) * t - 2 ≤ 2 * (G.edgeFinset.card : ℝ) / Fintype.card V →
          IsMinor H G := by
  sorry

end OMA.S_opg_forcing_a_2_regular_minor
