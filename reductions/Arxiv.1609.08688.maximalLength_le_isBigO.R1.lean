import FormalConjectures.Arxiv.«1609.08688».sIncreasingrTuples
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite

/-! Separate the tripartite graph bound from the encoding of two-increasing sequences. -/

open Arxiv.«1609.08688» SimpleGraph.TripartiteFromTriangles Filter

namespace OMA.R_Arxiv_1609_08688_maximalLength_le_isBigO_R1

/-- The quantitative Ruzsa–Szemerédi bound for tripartite graphs in which each edge lies in a unique triangle. -/
def H1 : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∀ t : Finset (Fin n × Fin n × Fin n), ExplicitDisjoint t → NoAccidental t →
      (t.card : ℝ) ≤ (n : ℝ)^2 / Real.exp (c * (Real.iteratedLog n : ℝ))

/-- A longest two-increasing sequence gives the same number of edge-disjoint triangles and no additional triangles. -/
def H2 : Prop :=
  ∀ n : ℕ, ∃ t : Finset (Fin n × Fin n × Fin n),
    t.card = maximalLength n ∧ ExplicitDisjoint t ∧ NoAccidental t

theorem main : H1 → H2 → type_of% @Arxiv.«1609.08688».maximalLength_le_isBigO := by
  intro hbound hrepresentation
  obtain ⟨c, hc, h⟩ := hbound
  refine ⟨c, hc, h.mono ?_⟩
  intro n hn
  obtain ⟨t, ht, hdisjoint, hno⟩ := hrepresentation n
  simpa only [ht] using hn t hdisjoint hno

end OMA.R_Arxiv_1609_08688_maximalLength_le_isBigO_R1