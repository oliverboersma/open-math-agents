import Mathlib

/-!
# Double-critical graph conjecture

Source: https://www.openproblemgarden.org/op/double_critical_graph_conjecture
Credit: @LAPRAI

*Reference:* P. Erdős, Problem 2, in: Theory of Graphs (Proc. Colloq., Tihany, 1966), Academic
Press, 1968, p. 361.

A connected simple graph `G` is *double-critical* if removing any pair of adjacent vertices lowers
the chromatic number by two. Conjecture: `Kₙ` is the only `n`-chromatic double-critical graph.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s; chromatic numbers are Mathlib's
  `SimpleGraph.chromaticNumber` (in `ℕ∞`, finite here).
* Removing the adjacent vertices `u, v` is the induced subgraph on the complement of `{u, v}`.
* *`Kₙ` is the only `n`-chromatic double-critical graph*: every double-critical graph is complete
  (`G = ⊤`). A complete graph on `n` vertices is `n`-chromatic, so for every `n` the only
  `n`-chromatic double-critical graph is then `Kₙ`, and conversely.
-/

namespace OMA.S_opg_double_critical_graph_conjecture

/-- `G` is double-critical: connected, and deleting the two ends of any edge lowers the chromatic
number by exactly two. -/
def IsDoubleCritical {V : Type} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ u v, G.Adj u v →
    (G.induce ({u, v} : Set V)ᶜ).chromaticNumber + 2 = G.chromaticNumber

/-- **Double-critical graph conjecture (Erdős–Lovász).** Every finite double-critical graph is
complete. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsDoubleCritical G → G = ⊤ := by
  sorry

end OMA.S_opg_double_critical_graph_conjecture
