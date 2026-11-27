import Mathlib

/-!
# Minimum number of arc-disjoint transitive subtournaments of order 3 in a tournament

Source: https://www.openproblemgarden.org/op/minimum_number_of_transitive_subtournaments_of_order_3_in_a_tournament
Credit: @LAPRAI

Conjecture: if `T` is a tournament of order `n`, then it contains `⌈n(n-1)/6 - n/3⌉` arc-disjoint
transitive subtournaments of order `3`.

## Encoding

* A tournament is a finite Mathlib `Digraph V` with no loops in which, for any two distinct
  vertices `u, v`, exactly one of the arcs `u → v`, `v → u` is present. Its order is `n = |V|`.
* A transitive subtournament of order `3` (a `TT₃`) is given by three vertices `a, b, c` with
  arcs `a → b`, `b → c`, `a → c` (they are then automatically distinct); its arcs are
  `(a, b), (b, c), (a, c)`.
* *Contains `m` arc-disjoint `TT₃`'s*: a family of `m` of them whose arc sets are pairwise
  disjoint, with `m = ⌈n(n-1)/6 - n/3⌉` computed in `ℚ` (and `0` when this is negative, via
  `Nat.ceil`; for `n ≤ 3` the bound is at most `0` anyway).
-/

namespace OMA.S_opg_minimum_number_of_transitive_subtournaments_of_order_3_in_a_tournament

/-- `G` is a tournament. -/
def IsTournament {V : Type} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ ∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u)

/-- `(a, b, c)` spans a transitive subtournament of order `3`: `a → b`, `b → c`, `a → c`. -/
def IsTT3 {V : Type} (G : Digraph V) (t : V × V × V) : Prop :=
  G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.1 t.2.2

/-- The three arcs of the triple `(a, b, c)`. -/
def arcs {V : Type} [DecidableEq V] (t : V × V × V) : Finset (V × V) :=
  {(t.1, t.2.1), (t.2.1, t.2.2), (t.1, t.2.2)}

/-- **Conjecture.** Every tournament of order `n` has `⌈n(n-1)/6 - n/3⌉` arc-disjoint `TT₃`'s. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V), IsTournament G →
    ∃ t : Fin ⌈((Fintype.card V : ℚ) * (Fintype.card V - 1) / 6 - Fintype.card V / 3)⌉₊ →
        V × V × V,
      (∀ i, IsTT3 G (t i)) ∧ ∀ i j, i ≠ j → Disjoint (arcs (t i)) (arcs (t j)) := by
  sorry

end OMA.S_opg_minimum_number_of_transitive_subtournaments_of_order_3_in_a_tournament
