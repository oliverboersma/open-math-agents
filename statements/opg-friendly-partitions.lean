import Mathlib

/-!
# Friendly partitions

Source: https://www.openproblemgarden.org/op/friendly_partitions
Credit: @LAPRAI

A friendly partition of a graph is a partition of the vertices into two sets so that every vertex
has at least as many neighbours in its own class as in the other. Problem: is it true that for
every `r`, all but finitely many `r`-regular graphs have friendly partitions?

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s.
* A partition into two sets has two nonempty classes `A` and `Aᶜ` (with a single class the
  condition is trivial; the source's discussion of the cubic case, which reduces to finding two
  vertex-disjoint cycles, confirms both classes are nonempty).
* *All but finitely many `r`-regular graphs*: up to isomorphism. Since there are finitely many
  graphs on a given number of vertices, this is equivalent to: there is `N` such that every
  `r`-regular graph with at least `N` vertices has a friendly partition.
* The source asks a yes/no question without conjecturing an answer; `main` states the answer
  yes, and a disproof would answer no.
-/

namespace OMA.S_opg_friendly_partitions

/-- `A, Aᶜ` is a friendly partition of `G`: both classes are nonempty and every vertex has at
least as many neighbours in its own class as in the other. -/
def IsFriendlyPartition {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) : Prop :=
  A.Nonempty ∧ Aᶜ.Nonempty ∧ ∀ v,
    ((G.neighborFinset v).filter (fun w => (w ∈ A ↔ v ∈ A))).card ≥
      ((G.neighborFinset v).filter (fun w => ¬ (w ∈ A ↔ v ∈ A))).card

/-- For every `r`, all but finitely many `r`-regular graphs have a friendly partition. -/
theorem main : ∀ r : ℕ, ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], N ≤ Fintype.card V → G.IsRegularOfDegree r →
    ∃ A : Finset V, IsFriendlyPartition G A := by
  sorry

end OMA.S_opg_friendly_partitions
