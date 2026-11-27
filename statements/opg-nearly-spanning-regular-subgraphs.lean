import Mathlib

/-!
# Nearly spanning regular subgraphs

Source: https://www.openproblemgarden.org/op/nearly_spanning_regular_subgraphs
Credit: @LAPRAI

Conjecture (Alon, Mubayi): for every `ε > 0` and every positive integer `k`, there exists
`r₀ = r₀(ε, k)` so that every simple `r`-regular graph `G` with `r ≥ r₀` has a `k`-regular
subgraph `H` with `|V(H)| ≥ (1 - ε) |V(G)|`.

## Encoding

* `G` is a `SimpleGraph` on a finite vertex type, `r`-regular (`G.IsRegularOfDegree r`).
* A subgraph `H` is given by its vertex set `S : Finset V` and a `SimpleGraph` `H ≤ G` whose
  edges have both ends in `S`. It is `k`-regular: every `v ∈ S` has exactly `k` neighbours in
  `H` (counted with `Nat.card`).
-/

namespace OMA.S_opg_nearly_spanning_regular_subgraphs

/-- **Alon–Mubayi conjecture.** -/
theorem main : ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 0 < k → ∃ r₀ : ℕ,
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ),
      r₀ ≤ r → G.IsRegularOfDegree r →
      ∃ (S : Finset V) (H : SimpleGraph V), H ≤ G ∧
        (∀ v w, H.Adj v w → v ∈ S) ∧
        (∀ v ∈ S, Nat.card {w : V // H.Adj v w} = k) ∧
        (1 - ε) * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := by
  sorry

end OMA.S_opg_nearly_spanning_regular_subgraphs
