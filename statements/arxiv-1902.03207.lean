import Mathlib

/-!
# Critical nearest-neighbour bond percolation

Duminil-Copin, Kozma and Tassion, arXiv:1902.03207v2, Conjecture 1 and §2.
Credit: @my-other-github-account
The pair (x,i) labels the undirected bond from x to x+e_i, once only.
The infinite-cluster event below is rooted at the origin as in Conjecture 1.
Model adapted from OpenAI, openai/math, CriticalPercolation/Model.lean
(3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0).
-/

namespace OMA.S_arxiv_1902_03207

abbrev Vertex (d : ℕ) := Fin d → ℤ
abbrev Bond (d : ℕ) := Vertex d × Fin d

def ends {d : ℕ} (b : Bond d) : Sym2 (Vertex d) :=
  s(b.1, b.1 + Pi.single b.2 1)

def atInfinity (d : ℕ) : Set (Set (Bond d)) :=
  {ω | {x | (SimpleGraph.fromEdgeSet (ends '' ω)).Reachable (0 : Vertex d) x}.Infinite}

noncomputable def theta (d : ℕ) (p : unitInterval) : ENNReal :=
  ProbabilityTheory.setBernoulli Set.univ p (atInfinity d)

noncomputable def critical (d : ℕ) : unitInterval := sInf {p | 0 < theta d p}

theorem main : ∀ d : ℕ, 2 ≤ d → theta d (critical d) = 0 := by
  sorry

end OMA.S_arxiv_1902_03207
