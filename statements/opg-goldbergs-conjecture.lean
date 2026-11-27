import Mathlib

/-!
# Goldberg's conjecture

Source: https://www.openproblemgarden.org/op/goldbergs_conjecture
Credit: @lzvxck

The source: the overfull parameter is
`w(G) = max_{H ⊆ G} ⌈ |E(H)| / ⌊|V(H)|/2⌋ ⌉`.
Conjecture: every graph `G` satisfies `χ'(G) ≤ max {Δ(G) + 1, w(G)}`.

Conventions: graphs are finite multigraphs without loops (parallel edges allowed, which is
the whole point: simple graphs satisfy the bound by Vizing's theorem). A multigraph is a finite
edge type `E` with an end map `ends : E → Sym2 V` whose values are never diagonal. In `w(G)`
the subgraphs `H` range over those with at least two vertices (otherwise `⌊|V(H)|/2⌋ = 0`).

The bound is stated in the equivalent form: if `k ≥ Δ(G) + 1` and `k ≥ w(G)`, then `G` has a
proper edge colouring with `k` colours. Here `k ≥ w(G)` means
`|E(H)| ≤ k * ⌊|V(H)|/2⌋` for every subgraph `H` with at least two vertices, and it suffices to
take for `H` the subgraph induced on each vertex set `S` (it has the most edges among subgraphs
with vertex set `S`). `Δ(G)` is the maximum number of edges at a vertex.
-/

namespace OMA.S_opg_goldbergs_conjecture

/-- **Goldberg's conjecture** (also Andersen, Seymour). A finite loopless multigraph has
chromatic index at most `max {Δ + 1, w}`, stated as: any `k` with `Δ + 1 ≤ k` and `w ≤ k`
admits a proper edge colouring with `k` colours. -/
theorem main : ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (ends : E → Sym2 V),
    (∀ e, ¬ (ends e).IsDiag) → ∀ k : ℕ,
      (∀ v : V, (Finset.univ.filter fun e => v ∈ ends e).card + 1 ≤ k) →
      (∀ S : Finset V, 2 ≤ S.card →
        (Finset.univ.filter fun e => ∀ v : V, v ∈ ends e → v ∈ S).card ≤ k * (S.card / 2)) →
      ∃ c : E → Fin k, ∀ e f, e ≠ f → (∃ v, v ∈ ends e ∧ v ∈ ends f) → c e ≠ c f := by
  sorry

end OMA.S_opg_goldbergs_conjecture
