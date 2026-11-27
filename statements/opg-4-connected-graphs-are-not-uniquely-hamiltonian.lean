import Mathlib

/-!
# A second Hamiltonian cycle in a 4-connected graph

Herbert Fleischner's conjecture as stated at
https://www.openproblemgarden.org/op/4_connected_graphs_are_not_uniquely_hamiltonian.
Lean statement by @dk8827.
-/

namespace OMA.S_opg_4_connected_graphs_are_not_uniquely_hamiltonian

open SimpleGraph

/-- A Hamiltonian cycle is represented by a spanning subgraph isomorphic to the cycle
on all vertices. Distinct spanning subgraphs correspond to distinct edge sets. -/
theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      4 < Fintype.card V →
      (∀ S : Finset V, S.card < 4 → (G.induce ((S : Set V)ᶜ)).Connected) →
      ∀ H : SimpleGraph V, H ≤ G →
        Nonempty (H ≃g cycleGraph (Fintype.card V)) →
        ∃ K : SimpleGraph V, K ≤ G ∧
          Nonempty (K ≃g cycleGraph (Fintype.card V)) ∧ K ≠ H := by
  sorry

end OMA.S_opg_4_connected_graphs_are_not_uniquely_hamiltonian
