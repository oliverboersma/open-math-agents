import Mathlib

/-!
# Forcing a K_6-minor

Source: https://www.openproblemgarden.org/op/forcing_a_k_6_minor
Credit: @lzvxck

The source states two conjectures (the first implies the second):
1. Every graph with minimum degree at least 7 contains a `K_6`-minor.
2. Every 7-connected graph contains a `K_6`-minor.
Both are stated here, as a conjunction.

Conventions: graphs are finite and simple, and nonempty in the first conjecture (so that the
minimum degree is defined). `G` contains a `K_6`-minor when there are six pairwise disjoint
vertex sets (branch sets), each inducing a connected subgraph, with an edge of `G` between any
two of them. `G` is `k`-connected when it has more than `k` vertices and deleting any set of
fewer than `k` vertices leaves it connected.
-/

namespace OMA.S_opg_forcing_a_k_6_minor

/-- `G` has a `K_n`-minor: `n` pairwise disjoint connected branch sets, any two joined by an
edge of `G`. -/
def HasCompleteMinor {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ B : Fin n → Set V, (∀ i, (G.induce (B i)).Connected) ∧
    (Pairwise fun i j => Disjoint (B i) (B j)) ∧
    ∀ i j, i ≠ j → ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y

/-- `G` is `k`-connected: more than `k` vertices, and deleting fewer than `k` vertices leaves
a connected graph. -/
def IsKConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

/-- **Forcing a `K_6`-minor.** Every nonempty finite graph of minimum degree at least 7 has a
`K_6`-minor, and every 7-connected finite graph has a `K_6`-minor. -/
theorem main :
    (∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, 7 ≤ G.degree v) → HasCompleteMinor G 6) ∧
    (∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      IsKConnected G 7 → HasCompleteMinor G 6) := by
  sorry

end OMA.S_opg_forcing_a_k_6_minor
