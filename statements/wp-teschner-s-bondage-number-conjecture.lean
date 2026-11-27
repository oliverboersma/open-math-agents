import Mathlib

/-!
# Teschner's bondage number conjecture

Source: https://en.wikipedia.org/wiki/bondage_number
Credit: @prophetlabs

Source statement (Wikipedia, *List of unsolved problems in mathematics*): is the bondage number
of a graph always less than or equal to `3/2` times its maximum degree?

Definitions (finite simple graphs):
* a dominating set of `G` is a set `D` of vertices such that every vertex is in `D` or adjacent
  to a vertex of `D`; the domination number `γ(G)` is the least size of a dominating set;
* the bondage number `b(G)` is the least number of edges whose removal increases `γ(G)`. It is
  defined when `G` has at least one edge (removing every edge then raises `γ` to `|V|`).

`b(G) ≤ (3/2) Δ(G)` holds iff some set `F` of edges whose removal increases `γ(G)` has
`2 |F| ≤ 3 Δ(G)`; this is the form stated below. The question is stated in its positive form.
-/

namespace OMA.S_wp_teschner_s_bondage_number_conjecture

open SimpleGraph

/-- `D` dominates `G`: every vertex lies in `D` or has a neighbour in `D`. -/
def IsDominatingSet {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v : V, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

/-- The domination number of `G`: the least size of a dominating set. -/
noncomputable def dominationNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ D : Finset V, IsDominatingSet G D ∧ D.card = k}

theorem main :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.Nonempty →
      ∃ F ⊆ G.edgeFinset,
        dominationNumber G < dominationNumber (G.deleteEdges (F : Set (Sym2 (Fin n)))) ∧
        2 * F.card ≤ 3 * G.maxDegree := by
  sorry

end OMA.S_wp_teschner_s_bondage_number_conjecture
