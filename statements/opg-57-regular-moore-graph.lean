import Mathlib

/-!
# 57-regular Moore graph?

Source: https://www.openproblemgarden.org/op/57_regular_moore_graph
Credit: @LAPRAI

*Reference:* A. J. Hoffman and R. R. Singleton, On Moore graphs with diameters 2 and 3,
IBM J. Res. Develop. 4 (1960), 497–504.

Question: does there exist a 57-regular graph with diameter 2 and girth 5?

## Encoding

* Graphs are Mathlib `SimpleGraph`s on a finite vertex type. Finiteness loses nothing: a
  `57`-regular graph of diameter `2` has at most `1 + 57 + 57 · 56` vertices.
* Diameter and girth are Mathlib's extended versions `SimpleGraph.ediam` and
  `SimpleGraph.egirth` (valued in `ℕ∞`, so a disconnected or acyclic graph cannot satisfy them
  by a junk value).
* The source asks a yes/no question without conjecturing an answer; `main` states the answer
  yes, and a disproof would answer no.
-/

namespace OMA.S_opg_57_regular_moore_graph

/-- There is a `57`-regular graph with diameter `2` and girth `5`. -/
theorem main : ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    G.IsRegularOfDegree 57 ∧ G.ediam = 2 ∧ G.egirth = 5 := by
  sorry

end OMA.S_opg_57_regular_moore_graph
