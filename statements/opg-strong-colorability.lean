import Mathlib

/-!
# Strong colorability

Source: https://www.openproblemgarden.org/op/strong_colorability
Credit: @LAPRAI

Let `r` be a positive integer. A graph `G` is strongly `r`-colorable if for every partition of
the vertices into sets of size at most `r` there is a proper `r`-coloring of `G` in which the
vertices in each set of the partition have distinct colors.

Conjecture (Aharoni, Alon, Haxell): if `Δ` is the maximal degree of a graph `G`, then `G` is
strongly `2Δ`-colorable.

## Encoding

* `G` is a finite `SimpleGraph`; `Δ = G.maxDegree`. Since the definition requires `r` positive,
  we assume `Δ ≥ 1` (for `Δ = 0` there is no positive `2Δ`).
* A partition of the vertices into sets of size at most `r` is given by a labelling
  `part : V → V` (the blocks are the nonempty fibres), each fibre having at most `r` elements.
* A proper `r`-coloring is `c : V → Fin r` with `c u ≠ c v` whenever `u` and `v` are adjacent;
  the vertices of each block get distinct colors: `part u = part v → u ≠ v → c u ≠ c v`.
-/

namespace OMA.S_opg_strong_colorability

/-- `G` is strongly `r`-colorable. -/
def IsStronglyColorable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : ℕ) :
    Prop :=
  ∀ part : V → V, (∀ x, (Finset.univ.filter (fun v => part v = x)).card ≤ r) →
    ∃ c : V → Fin r, (∀ u v, G.Adj u v → c u ≠ c v) ∧
      ∀ u v, part u = part v → u ≠ v → c u ≠ c v

/-- **Aharoni–Alon–Haxell conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    1 ≤ G.maxDegree → IsStronglyColorable G (2 * G.maxDegree) := by
  sorry

end OMA.S_opg_strong_colorability
