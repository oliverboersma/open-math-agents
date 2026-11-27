import Mathlib

/-!
# Monochromatic reachability vs rainbow triangles

Source: https://www.openproblemgarden.org/op/monochromatic_reachability_vs_rainbow_triangles
Credit: @LAPRAI

Problem (Sands, Sauer, Woodrow): let `G` be a tournament with edges colored from a set of three
colors. Is it true that `G` must have either a rainbow directed cycle of length three or a vertex
`v` so that every other vertex can be reached from `v` by a monochromatic (directed) path?
We state the positive answer.

## Encoding

* A tournament is a Mathlib `Digraph` on a finite vertex type with no loops and, for any two
  distinct vertices, exactly one of the two arcs between them.
* A 3-coloring of the arcs is a function `col : V → V → Fin 3`; only its values on arcs matter.
* A rainbow directed cycle of length three is `a → b → c → a` whose three arcs have pairwise
  distinct colors (such `a, b, c` are automatically distinct, since `G` has no loops and no
  pair of opposite arcs).
* `w` is reachable from `v` by a monochromatic directed path if for some color `k` there is a
  directed walk from `v` to `w` using only arcs of color `k` (`Relation.TransGen`); a shortest
  such walk is a path.
-/

namespace OMA.S_opg_monochromatic_reachability_vs_rainbow_triangles

/-- `G` is a tournament. -/
def IsTournament {V : Type} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ ∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u)

/-- **Sands–Sauer–Woodrow problem**, positive answer. -/
theorem main : ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) (col : V → V → Fin 3),
    IsTournament G →
    (∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        col a b ≠ col b c ∧ col b c ≠ col c a ∧ col a b ≠ col c a) ∨
    (∃ v : V, ∀ w : V, w ≠ v → ∃ k : Fin 3,
        Relation.TransGen (fun x y => G.Adj x y ∧ col x y = k) v w) := by
  sorry

end OMA.S_opg_monochromatic_reachability_vs_rainbow_triangles
