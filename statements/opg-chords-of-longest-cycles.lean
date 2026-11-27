import Mathlib

/-!
# Chords of longest cycles

Source: https://www.openproblemgarden.org/op/chords_of_longest_cycles
Credit: @LAPRAI

Conjecture (Thomassen): if `G` is a 3-connected graph, every longest cycle in `G` has a chord.
A chord of a cycle `C` is an edge `e` with `e ∉ E(C)` whose two ends are both in `V(C)`.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s.
* `k`-connected (standard definition): more than `k` vertices, and deleting any set of fewer than
  `k` vertices leaves a connected graph. Mathlib has no vertex-connectivity notion, so it is
  defined here.
* A cycle is a closed walk `c` with `c.IsCycle`; it is *longest* if no cycle of `G` is longer.
* A chord of `c` is an edge `xy` of `G`, not an edge of `c`, with `x` and `y` on `c`.
-/

namespace OMA.S_opg_chords_of_longest_cycles

variable {V : Type} [Fintype V]

/-- `G` is `k`-connected: it has more than `k` vertices and stays connected after deleting any
set of fewer than `k` vertices. -/
def IsKConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Finset V, S.card < k → (G.induce (↑S : Set V)ᶜ).Connected

/-- `c` is a longest cycle of `G`. -/
def IsLongestCycle {G : SimpleGraph V} {u : V} (c : G.Walk u u) : Prop :=
  c.IsCycle ∧ ∀ (v : V) (c' : G.Walk v v), c'.IsCycle → c'.length ≤ c.length

/-- The cycle `c` has a chord. -/
def HasChord {G : SimpleGraph V} {u : V} (c : G.Walk u u) : Prop :=
  ∃ x y, G.Adj x y ∧ x ∈ c.support ∧ y ∈ c.support ∧ s(x, y) ∉ c.edges

/-- **Thomassen's chord conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsKConnected G 3 →
    ∀ (u : V) (c : G.Walk u u), IsLongestCycle c → HasChord c := by
  sorry

end OMA.S_opg_chords_of_longest_cycles
