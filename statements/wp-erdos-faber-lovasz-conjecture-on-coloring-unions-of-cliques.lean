import Mathlib

/-!
# Erdős–Faber–Lovász conjecture on coloring unions of cliques

Source: https://en.wikipedia.org/wiki/Erdős–Faber–Lovász_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source statement (Erdős, Faber, Lovász, 1972): if `k` complete graphs, each having exactly `k`
vertices, have the property that every pair of complete graphs has at most one shared vertex,
then the union of the graphs can be properly colored with `k` colors.
(The source reports a proof for all sufficiently large `k` by Kang–Kelly–Kühn–Methuku–Osthus;
the statement for every `k` is what is stated here.)

Conventions:
* the `k` complete graphs are given by their vertex sets `C i : Finset V`, `i : Fin k`, each of
  size exactly `k`; the complete graph on `C i` has every pair of distinct vertices of `C i`
  adjacent;
* every pair of complete graphs has at most one shared vertex: `#(C i ∩ C j) ≤ 1` for `i ≠ j`;
* the union of the graphs is the simple graph `unionGraph C` whose vertices are those of `V`,
  and in which distinct `x, y` are adjacent when some `C i` contains both. We require every
  vertex of `V` to lie in some `C i`, so that `V` is exactly the vertex set of the union (this
  only rules out extra isolated vertices, and keeps the degenerate case `k = 0` correct);
* properly colored with `k` colors is Mathlib's `SimpleGraph.Colorable k`.
-/

namespace OMA.S_wp_erdos_faber_lovasz_conjecture_on_coloring_unions_of_cliques

/-- The union of the complete graphs on the vertex sets `C i`: distinct `x, y` are adjacent
iff some `C i` contains both (`SimpleGraph.fromRel` adds `x ≠ y` and symmetrises, which is
redundant here since the relation is already symmetric). -/
def unionGraph {V : Type} {k : ℕ} (C : Fin k → Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => ∃ i, x ∈ C i ∧ y ∈ C i)

theorem main : ∀ (V : Type) [DecidableEq V] (k : ℕ) (C : Fin k → Finset V),
    (∀ i, (C i).card = k) →
    (∀ i j, i ≠ j → (C i ∩ C j).card ≤ 1) →
    (∀ v : V, ∃ i, v ∈ C i) →
    (unionGraph C).Colorable k := by
  sorry

end OMA.S_wp_erdos_faber_lovasz_conjecture_on_coloring_unions_of_cliques
