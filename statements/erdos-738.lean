import Mathlib

/-!
# Erdős Problem 738

Source: https://www.erdosproblems.com/738
Credit: @timlantin

If $G$ has infinite chromatic number and is triangle-free (contains no $K_3$) then must $G$
contain every tree as an induced subgraph?

A conjecture of Gyárfás [Er81]. By the de Bruijn–Erdős theorem, a graph of infinite chromatic
number has finite subgraphs of every chromatic number, so this would follow from the triangle-free
case of the Gyárfás–Sumner conjecture.

Formalization notes:
* `G` may be infinite: its vertex type `V` is arbitrary. Infinite chromatic number is
  `G.chromaticNumber = ⊤`, i.e. `G` admits no proper colouring with finitely many colours.
* Triangle-free is `G.CliqueFree 3`.
* A tree means a finite tree, and containment is as an induced subgraph,
  `SimpleGraph.IsIndContained`.
-/

namespace OMA.S_erdos_738

/-- Every triangle-free graph of infinite chromatic number contains every finite tree as an
induced subgraph. -/
theorem main : ∀ {V : Type} (G : SimpleGraph V), G.chromaticNumber = ⊤ → G.CliqueFree 3 →
    ∀ {W : Type} [Fintype W] (T : SimpleGraph W), T.IsTree → T.IsIndContained G := by
  sorry

end OMA.S_erdos_738
