import Mathlib

/-!
# A Conjecture on Induced Subgraphs of Cayley Graphs

Source: https://arxiv.org/abs/2003.13166 (Potechin, Tsang), Conjecture 1.
Credit: @Genbox

Definition 1.1 of the source: for a group `G` and a set `S` of non-identity elements of `G` which is
symmetric (`s ∈ S → s⁻¹ ∈ S`), the Cayley graph `Γ(G,S)` is the undirected graph with vertex set `G`
and edges `{g, s g}` for `g ∈ G`, `s ∈ S`.

Conjecture 1: for any Cayley graph `X = Γ(G,S)` on a group `G` and any generating set `S`, if
`U ⊆ G` has `|U| > |G|/2`, then the induced subgraph `X(U)` has maximum degree at least
`√(|S|/2)`.

The maximum degree of `X(U)` is at least `x` iff some `u ∈ U` has at least `x` neighbours in `U`.
`SimpleGraph.fromRel` symmetrizes the relation `h = s * g`; for symmetric `S` without the identity
this is exactly `Γ(G,S)`. The group is finite (the statement compares `|U|` with `|G|/2`).
-/

namespace OMA.S_arxiv_2003_13166

/-- The Cayley graph `Γ(G,S)`: `g ~ s * g` for `s ∈ S`. -/
def cayley {G : Type*} [Group G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel fun g h => ∃ s ∈ S, h = s * g

theorem main : ∀ (G : Type) [Group G] [Finite G] (S : Set G), (1 : G) ∉ S →
    (∀ s ∈ S, s⁻¹ ∈ S) → Subgroup.closure S = ⊤ →
    ∀ U : Set G, Nat.card G < 2 * U.ncard →
      ∃ u ∈ U, Real.sqrt ((S.ncard : ℝ) / 2) ≤
        ({v | v ∈ U ∧ (cayley S).Adj u v}.ncard : ℝ) := by
  sorry

end OMA.S_arxiv_2003_13166
