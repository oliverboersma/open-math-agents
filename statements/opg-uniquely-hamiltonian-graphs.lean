import Mathlib

/-!
# R-regular graphs are not uniquely hamiltonian

Source: https://www.openproblemgarden.org/op/uniquely_hamiltonian_graphs
Credit: @lzvxck

The source: if `G` is a finite `r`-regular graph, where `r > 2`, then `G` is not uniquely
hamiltonian (a graph is uniquely hamiltonian if it contains precisely one Hamiltonian cycle).

Conventions: graphs are finite and simple. A Hamilton cycle is a cycle through every vertex;
two Hamilton cycles are different when their edge sets differ (so a cycle, its reversal and its
rotations count as the same cycle). Not uniquely hamiltonian is stated as: whenever `G` has a
Hamilton cycle, it has a second one.
-/

namespace OMA.S_opg_uniquely_hamiltonian_graphs

/-- `c` is a Hamilton cycle of `G`: a cycle visiting every vertex. -/
def IsHamiltonCycle {V : Type*} (G : SimpleGraph V) {v : V} (c : G.Walk v v) : Prop :=
  c.IsCycle ∧ ∀ w, w ∈ c.support

/-- **Regular graphs are not uniquely hamiltonian (Sheehan).** If `G` is a finite `r`-regular
graph with `r > 2` and `G` has a Hamilton cycle, then `G` has a second Hamilton cycle (with a
different edge set). -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ), 2 < r → G.IsRegularOfDegree r →
      ∀ (v : V) (c : G.Walk v v), IsHamiltonCycle G c →
        ∃ (w : V) (d : G.Walk w w), IsHamiltonCycle G d ∧
          d.edges.toFinset ≠ c.edges.toFinset := by
  sorry

end OMA.S_opg_uniquely_hamiltonian_graphs
