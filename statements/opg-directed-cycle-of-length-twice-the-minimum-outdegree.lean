import Mathlib

/-!
# Directed path of length twice the minimum outdegree

Source: https://www.openproblemgarden.org/op/directed_cycle_of_length_twice_the_minimum_outdegree
Credit: @LAPRAI

Conjecture (Thomassé): every oriented graph with minimum outdegree `k` contains a directed path
of length `2k`. (The page's URL mentions a cycle, but its title and the conjecture itself are
about a directed path; this file states the conjecture as written.)

## Encoding

* An oriented graph is a finite, nonempty Mathlib `Digraph V` with no pair of opposite arcs
  (`u → v` and `v → u`), hence in particular no loops.
* *Minimum outdegree `k`*: every vertex has at least `k` out-neighbours (a graph of minimum
  outdegree exactly `k` satisfies this, and the conclusion only gets weaker as `k` decreases, so
  this is the same statement).
* A directed path of length `2k` has `2k` arcs: an injective sequence of `2k + 1` vertices
  `p 0, …, p (2k)` with an arc from `p i` to `p (i + 1)` for each `i < 2k`.
-/

namespace OMA.S_opg_directed_cycle_of_length_twice_the_minimum_outdegree

/-- An oriented graph: no two opposite arcs (so also no loops). -/
def IsOriented {V : Type} (G : Digraph V) : Prop :=
  ∀ u v, G.Adj u v → ¬ G.Adj v u

/-- The outdegree of `v`: the number of out-neighbours. -/
def outdegree {V : Type} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w)).card

/-- `G` contains a directed path of length `ℓ` (with `ℓ` arcs and `ℓ + 1` distinct vertices). -/
def HasDirectedPathOfLength {V : Type} (G : Digraph V) (ℓ : ℕ) : Prop :=
  ∃ p : Fin (ℓ + 1) → V, Function.Injective p ∧ ∀ i : Fin ℓ, G.Adj (p i.castSucc) (p i.succ)

/-- **Thomassé's conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (k : ℕ), IsOriented G → (∀ v, k ≤ outdegree G v) → HasDirectedPathOfLength G (2 * k) := by
  sorry

end OMA.S_opg_directed_cycle_of_length_twice_the_minimum_outdegree
