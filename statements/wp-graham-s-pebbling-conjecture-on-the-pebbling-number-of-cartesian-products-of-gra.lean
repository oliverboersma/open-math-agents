import Mathlib

/-!
# Graham's pebbling conjecture on the pebbling number of Cartesian products of graphs

Source: https://en.wikipedia.org/wiki/Graham's_pebbling_conjecture
(redirects to https://en.wikipedia.org/wiki/Graph_pebbling#Graham's_pebbling_conjecture)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source definitions: a pebbling move on a graph consists of choosing a vertex with at least two
pebbles, removing two pebbles from it, and adding one to an adjacent vertex. The pebbling number
`π(G)` is the lowest natural number `n` such that, given any target (root) vertex and any initial
configuration of `n` pebbles, it is possible, after a possibly empty series of pebbling moves,
to reach a configuration in which the root has one or more pebbles.

Graham's pebbling conjecture (credited to Graham by Chung, 1989): the pebbling number of a
Cartesian product of graphs is at most the product of the pebbling numbers of the factors,
`π(G □ H) ≤ π(G) π(H)`.

Conventions:
* graphs are finite simple graphs; they are assumed connected, as in Chung's paper: for a
  disconnected graph no `n` satisfies the defining condition, so `π` is only defined for
  connected graphs (and then the defining set is non-empty, so the `sInf` below is a genuine
  minimum, not a junk value);
* a configuration is `c : V → ℕ` (zero or more pebbles on each vertex) and `n` pebbles means
  `∑ v, c v = n`;
* a pebbling move from `u` to an adjacent `v` with `2 ≤ c u` gives
  `update (update c u (c u - 2)) v (c v + 1)`; a series of moves is `Relation.ReflTransGen`;
* the Cartesian product is Mathlib's `SimpleGraph.boxProd` (`G □ H`).
-/

namespace OMA.S_wp_graham_s_pebbling_conjecture_on_the_pebbling_number_of_cartesian_products_of_gra

variable {V : Type} [Fintype V] [DecidableEq V]

/-- One pebbling move on `G`: take two pebbles from `u` (which has at least two) and put one on
an adjacent vertex `v`. -/
def PebbleMove (G : SimpleGraph V) (c c' : V → ℕ) : Prop :=
  ∃ u v, G.Adj u v ∧ 2 ≤ c u ∧
    c' = Function.update (Function.update c u (c u - 2)) v (c v + 1)

/-- Every configuration of `n` pebbles can move a pebble onto any root. -/
def Solvable (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ c : V → ℕ, ∑ v, c v = n → ∀ r : V,
    ∃ c', Relation.ReflTransGen (PebbleMove G) c c' ∧ 1 ≤ c' r

/-- The pebbling number: the lowest `n` with `Solvable G n`. -/
noncomputable def pebblingNumber (G : SimpleGraph V) : ℕ :=
  sInf {n | Solvable G n}

theorem main : ∀ (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W), G.Connected → H.Connected →
    pebblingNumber (G □ H) ≤ pebblingNumber G * pebblingNumber H := by
  sorry

end OMA.S_wp_graham_s_pebbling_conjecture_on_the_pebbling_number_of_cartesian_products_of_gra
