import Mathlib

/-!
# Unfriendly partition conjecture

Source: https://en.wikipedia.org/wiki/unfriendly_partition
Credit: @prophetlabs

Source statement (Wikipedia, *List of unsolved problems in mathematics*): does every countable
graph have an unfriendly partition into two parts?

An unfriendly partition of a graph `G` into two parts is a partition of its vertex set into two
sets such that every vertex has at least as many neighbours in the other part as in its own part.
For vertices of infinite degree the comparison is between cardinalities. A partition into two
parts is encoded by a colouring `f : V → Bool` (one of the parts may be empty). Countable graphs
include finite ones. The question is stated here in its positive form.
-/

namespace OMA.S_wp_unfriendly_partition_conjecture

open SimpleGraph

/-- `f` is an unfriendly 2-partition of `G`: every vertex has at least as many neighbours on the
other side as on its own side (compared as cardinalities). -/
def IsUnfriendlyPartition {V : Type*} (G : SimpleGraph V) (f : V → Bool) : Prop :=
  ∀ v : V, Cardinal.mk {w // G.Adj v w ∧ f w = f v} ≤ Cardinal.mk {w // G.Adj v w ∧ f w ≠ f v}

theorem main :
    ∀ (V : Type) [Countable V] (G : SimpleGraph V), ∃ f : V → Bool, IsUnfriendlyPartition G f := by
  sorry

end OMA.S_wp_unfriendly_partition_conjecture
