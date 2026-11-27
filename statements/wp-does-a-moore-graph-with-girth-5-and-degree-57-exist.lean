import Mathlib

/-!
# Does a Moore graph with girth 5 and degree 57 exist?

Source: https://en.wikipedia.org/wiki/Moore_graph
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: a **Moore graph** of degree `k` and girth `5` has `k ^ 2 + 1` vertices: a root, its `k`
neighbours, and `k * (k - 1)` vertices at distance two, all distinct because there are no triangles
or squares.  Moore graphs of girth `5` are known to exist exactly for the degrees `2, 3, 7` and
possibly `57`; whether a Moore graph of degree `57` exists is open.

So the proposition formalized below is: there is a simple graph on `3250 = 57 ^ 2 + 1` vertices in
which every vertex has exactly `57` neighbours and which has no cycles of length `3` or `4`.
-/

namespace OMA.S_wp_does_a_moore_graph_with_girth_5_and_degree_57_exist

-- definitions the statement needs (no sorry, no axiom)

/-- Every vertex of `G` has exactly `k` neighbours. -/
noncomputable def DegreeIs (G : SimpleGraph (Fin 3250)) (k : ℕ) : Prop := by
  classical
  exact ∀ v : Fin 3250, (Finset.univ.filter (fun w : Fin 3250 => G.Adj v w)).card = k

/-- `G` has no triangles. -/
def TriangleFree (G : SimpleGraph (Fin 3250)) : Prop :=
  ∀ a b c : Fin 3250, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)

/-- `G` has no cycles of length four: four distinct vertices joined cyclically do not occur. -/
def SquareFree (G : SimpleGraph (Fin 3250)) : Prop :=
  ∀ a b c d : Fin 3250,
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → ¬ (a ≠ c ∧ b ≠ d)

/-- Does a Moore graph with girth 5 and degree 57 exist? -/
theorem main : ∃ G : SimpleGraph (Fin 3250),
    DegreeIs G 57 ∧ TriangleFree G ∧ SquareFree G := by
  sorry

end OMA.S_wp_does_a_moore_graph_with_girth_5_and_degree_57_exist
