import Mathlib

/-!
# 4-regular 4-chromatic graphs of high girth

Source: https://www.openproblemgarden.org/op/high_girth_low_degree_4_chromatic_graphs
Credit: @LAPRAI

Problem: do there exist 4-regular 4-chromatic graphs of arbitrarily high girth?
(A case of Grünbaum's conjecture, which is false in general by Johansson's theorem.)

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s.
* *Arbitrarily high girth*: for every `g` there is such a graph of girth at least `g`, using
  Mathlib's extended girth `SimpleGraph.egirth` (a finite 4-regular graph has cycles, so its
  girth is finite).
* `4`-chromatic: `chromaticNumber = 4`.
* The source asks a yes/no question without conjecturing an answer; `main` states the answer
  yes, and a disproof would answer no.
-/

namespace OMA.S_opg_high_girth_low_degree_4_chromatic_graphs

/-- For every `g` there is a finite `4`-regular `4`-chromatic graph of girth at least `g`. -/
theorem main : ∀ g : ℕ, ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    G.IsRegularOfDegree 4 ∧ G.chromaticNumber = 4 ∧ (g : ℕ∞) ≤ G.egirth := by
  sorry

end OMA.S_opg_high_girth_low_degree_4_chromatic_graphs
