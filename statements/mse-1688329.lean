import Mathlib

/-!
# Existence of a cycle of length $2^k$?

Source: https://math.stackexchange.com/questions/1688329/existence-of-a-cycle-of-length-2k
Credit: @mgv27

Show that if each vertex of a graph has degree $\geq 3$, then it has a cycle whose length is
some power of $2$. (The asker could only show that there is an even cycle.)

Formalization notes:
* This is the Erdős–Gyárfás conjecture, which is open; `main` states the expected "yes".
* Graphs are finite simple graphs on a nonempty finite vertex type `V` with minimum degree
  at least `3` (written as `3 ≤ G.degree v` for every `v`).
* A cycle is a `SimpleGraph.Walk.IsCycle`; its length is the walk length. Every cycle has
  length `≥ 3`, so the power of two is automatically `2^k` with `k ≥ 2`.
* Nonemptiness of `V` is required, since otherwise the degree condition holds vacuously.
-/

namespace OMA.S_mse_1688329

/-- `G` has a cycle whose length is a power of two. -/
def HasPowerOfTwoCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (u : V) (p : G.Walk u u) (k : ℕ), p.IsCycle ∧ p.length = 2 ^ k

/-- Erdős–Gyárfás: every finite graph with minimum degree at least 3 has a cycle of length a
power of two. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, 3 ≤ G.degree v) → HasPowerOfTwoCycle G := by
  sorry

end OMA.S_mse_1688329
