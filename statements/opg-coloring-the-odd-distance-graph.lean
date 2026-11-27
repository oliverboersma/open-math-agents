import Mathlib

/-!
# Coloring the Odd Distance Graph

Source: https://www.openproblemgarden.org/op/coloring_the_odd_distance_graph
Credit: @LAPRAI

The Odd Distance Graph `𝒪` is the graph with vertex set `ℝ²` in which two points are adjacent if
the distance between them is an odd integer. Question: is `χ(𝒪) = ∞`?

## Encoding

* `ℝ²` is `EuclideanSpace ℝ (Fin 2)` with its Euclidean distance.
* Two distinct points are adjacent iff their distance is `k` for some odd natural number `k`
  (`SimpleGraph.fromRel` adds distinctness and symmetry; both are automatic here anyway).
* `χ` is Mathlib's `SimpleGraph.chromaticNumber`, valued in `ℕ∞`; `χ = ∞` means there is no
  proper colouring with finitely many colours (no measurability is required, as in the source's
  main question; the measurable variant is a separate, known result).
* The source asks a yes/no question without conjecturing an answer; `main` states the answer
  yes, and a disproof would answer no.
-/

namespace OMA.S_opg_coloring_the_odd_distance_graph

/-- The odd distance graph on the Euclidean plane. -/
def oddDistanceGraph : SimpleGraph (EuclideanSpace ℝ (Fin 2)) :=
  SimpleGraph.fromRel (fun x y => ∃ k : ℕ, Odd k ∧ dist x y = k)

/-- The odd distance graph has infinite chromatic number. -/
theorem main : oddDistanceGraph.chromaticNumber = ⊤ := by
  sorry

end OMA.S_opg_coloring_the_odd_distance_graph
