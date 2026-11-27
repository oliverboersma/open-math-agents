import Mathlib

/-!
# Seymour's r-graph conjecture

Source: https://www.openproblemgarden.org/op/seymours_r_graph_conjecture
Credit: @lzvxck

The source: an `r`-graph is an `r`-regular graph `G` with the property that `|δ(X)| ≥ r` for
every `X ⊆ V(G)` with odd size. Conjecture: `χ'(G) ≤ r + 1` for every `r`-graph `G`.

Conventions: graphs are finite multigraphs without loops (parallel edges allowed, as in the
source's setting; for simple graphs the bound is Vizing's theorem). A multigraph is a finite
edge type `E` with an end map `ends : E → Sym2 V` whose values are never diagonal. `r`-regular
means every vertex lies on exactly `r` edges, and `δ(X)` is the set of edges with one end in
`X` and the other outside `X`. `χ'(G) ≤ r + 1` is stated as the existence of a proper edge
colouring with `r + 1` colours (edges sharing an end get different colours).
-/

namespace OMA.S_opg_seymours_r_graph_conjecture

/-- **Seymour's r-graph conjecture.** Every `r`-graph (a loopless `r`-regular multigraph in
which every odd vertex set has at least `r` edges leaving it) is `(r + 1)`-edge-colourable. -/
theorem main : ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (ends : E → Sym2 V),
    (∀ e, ¬ (ends e).IsDiag) → ∀ r : ℕ,
      (∀ v : V, (Finset.univ.filter fun e => v ∈ ends e).card = r) →
      (∀ X : Finset V, Odd X.card →
        r ≤ (Finset.univ.filter fun e =>
          (∃ v : V, v ∈ ends e ∧ v ∈ X) ∧ ∃ v : V, v ∈ ends e ∧ v ∉ X).card) →
      ∃ c : E → Fin (r + 1), ∀ e f, e ≠ f → (∃ v, v ∈ ends e ∧ v ∈ ends f) → c e ≠ c f := by
  sorry

end OMA.S_opg_seymours_r_graph_conjecture
