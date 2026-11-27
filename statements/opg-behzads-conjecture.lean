import Mathlib

/-!
# Total Colouring Conjecture (Behzad)

Source: https://www.openproblemgarden.org/op/behzads_conjecture

A total coloring of a graph G = (V, E) is an assignment of colors to the vertices and the
edges of G such that every pair of adjacent vertices, every pair of adjacent edges and
every vertex and incident edge pair receive different colors. The total chromatic number
χ''(G) is the minimum number of colors needed in a total coloring of G.

Conjecture (Behzad). For every graph G, χ''(G) = Δ(G) + 1 or Δ(G) + 2, where Δ(G) is the
maximum degree of a vertex of G.

Conventions:
* G is a finite simple graph (`SimpleGraph V`, `Fintype V`) with at least one vertex.
  For the graph with no vertices χ'' = 0 while Δ = 0, so that degenerate case is excluded,
  as is customary (a graph has a nonempty vertex set).
* A total coloring with k colors is a pair `cv : V → Fin k`, `ce : G.edgeSet → Fin k` with
  - adjacent vertices: `G.Adj u v → cv u ≠ cv v`;
  - adjacent edges: two distinct edges sharing an endpoint get different colors;
  - incidence: an edge and each of its endpoints get different colors.
* `totalChromaticNumber G` is the least k admitting a total coloring with k colors
  (`sInf` over ℕ; the set is nonempty since coloring all vertices and edges with distinct
  colors works, so the infimum is a genuine minimum).
* Δ(G) is Mathlib's `G.maxDegree`.
-/

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

namespace OMA.S_opg_behzads_conjecture

/-- `cv`, `ce` form a total coloring of `G`. -/
def IsTotalColoring {V α : Type} (G : SimpleGraph V) (cv : V → α) (ce : G.edgeSet → α) :
    Prop :=
  (∀ u v : V, G.Adj u v → cv u ≠ cv v) ∧
  (∀ e f : G.edgeSet, e ≠ f → (∃ v : V, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) →
    ce e ≠ ce f) ∧
  (∀ (e : G.edgeSet) (v : V), v ∈ (e : Sym2 V) → ce e ≠ cv v)

/-- The total chromatic number χ''(G). -/
noncomputable def totalChromaticNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ (cv : V → Fin k) (ce : G.edgeSet → Fin k), IsTotalColoring G cv ce}

theorem main :
    ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      totalChromaticNumber G = G.maxDegree + 1 ∨
        totalChromaticNumber G = G.maxDegree + 2 := by
  sorry

end OMA.S_opg_behzads_conjecture
