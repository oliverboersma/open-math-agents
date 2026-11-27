import Mathlib

/-!
# Hamiltonian cycles in line graphs

Source: https://www.openproblemgarden.org/op/hamiltonian_cycles_in_line_graphs
Credit: @LAPRAI

Conjecture (Thomassen): every 4-connected line graph is hamiltonian.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s. A *line graph* is a graph isomorphic to
  `H.lineGraph` (Mathlib's line graph, on the edge set of `H`) for some simple graph `H`.
* `k`-connected (standard definition): more than `k` vertices, and deleting any set of fewer than
  `k` vertices leaves a connected graph. Mathlib has no vertex-connectivity notion, so it is
  defined here.
* *Hamiltonian* is Mathlib's `SimpleGraph.IsHamiltonian` (a Hamiltonian cycle exists; a
  4-connected graph has at least 5 vertices, so Mathlib's convention for one vertex is irrelevant).
-/

namespace OMA.S_opg_hamiltonian_cycles_in_line_graphs

/-- `G` is `k`-connected: it has more than `k` vertices and stays connected after deleting any
set of fewer than `k` vertices. -/
def IsKConnected {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Finset V, S.card < k → (G.induce (↑S : Set V)ᶜ).Connected

/-- `G` is a line graph: it is isomorphic to the line graph of some simple graph. -/
def IsLineGraph {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (W : Type) (H : SimpleGraph W), Nonempty (G ≃g H.lineGraph)

/-- **Thomassen's conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsLineGraph G → IsKConnected G 4 → G.IsHamiltonian := by
  sorry

end OMA.S_opg_hamiltonian_cycles_in_line_graphs
