import Mathlib

/-!
# Seymour's Second Neighbourhood Conjecture

Source: https://www.openproblemgarden.org/op/seymours_second_neighbourhood_conjecture
Credit: @LAPRAI

Any oriented graph has a vertex whose outdegree is at most its second outdegree. The `n`-th
outdegree of `v` is the number of vertices `w` for which the minimal outward-directed path from
`v` to `w` has length `n`.

## Encoding

* An oriented graph is a finite, nonempty Mathlib `Digraph V` with no pair of opposite arcs
  (`u → v` and `v → u`), hence in particular no loops. (For an empty vertex set the claim fails
  vacuously, and the source's graphs have vertices.)
* The first outdegree of `v` counts the `w` at directed distance `1`: the out-neighbours.
* The second outdegree of `v` counts the `w` at directed distance exactly `2`: `w ≠ v`, `w` is
  not an out-neighbour of `v`, and `v → u → w` for some `u`.
-/

namespace OMA.S_opg_seymours_second_neighbourhood_conjecture

/-- An oriented graph: no two opposite arcs (so also no loops). -/
def IsOriented {V : Type} (G : Digraph V) : Prop :=
  ∀ u v, G.Adj u v → ¬ G.Adj v u

/-- The outdegree of `v`: the number of out-neighbours. -/
def outdegree {V : Type} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w)).card

/-- The second outdegree of `v`: the number of vertices at directed distance exactly `2`. -/
def secondOutdegree {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (v : V) : ℕ :=
  (Finset.univ.filter (fun w => w ≠ v ∧ ¬ G.Adj v w ∧ ∃ u, G.Adj v u ∧ G.Adj u w)).card

/-- **Seymour's second neighbourhood conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : Digraph V)
    [DecidableRel G.Adj], IsOriented G → ∃ v, outdegree G v ≤ secondOutdegree G v := by
  sorry

end OMA.S_opg_seymours_second_neighbourhood_conjecture
