import Mathlib

/-!
# Minimum number of edges in an indecomposable loopless multigraph

Tanny Libman asks for a degree-dependent lower bound and extremal examples.
The question explicitly allows separate copies of an edge to lie in different
parts. We state the sharp bound, including attainment, and the degrees for
which no such multigraph exists. The empty edge set has maximum degree zero.

Source: https://mathoverflow.net/questions/488874
-/

namespace OMA.S_mo_488874

/-- A finite loopless multigraph, with each edge type recording its multiplicity.
Orientations record the endpoints only. -/
structure Multigraph (V E : Type*) where
  source : E → V
  target : E → V
  no_loops : ∀ e, source e ≠ target e
  multiplicity : E → ℕ

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

def Multigraph.degree (G : Multigraph V E) (c : E → ℕ) (v : V) : ℕ :=
  ∑ e, if v = G.source e ∨ v = G.target e then c e else 0

def Multigraph.maxDegree (G : Multigraph V E) (c : E → ℕ) : ℕ :=
  Finset.univ.sup (G.degree c)

def Multigraph.edges (G : Multigraph V E) : ℕ := ∑ e, G.multiplicity e

def Multigraph.indecomposable (G : Multigraph V E) : Prop :=
  ∀ x y : E → ℕ, (∀ e, x e+y e = G.multiplicity e) →
    (∃ e, 0 < x e) → (∃ e, 0 < y e) →
      G.maxDegree G.multiplicity < G.maxDegree x + G.maxDegree y

/-- Attainable edge counts among graphs satisfying the strict split inequality. -/
def counts (r : ℕ) : Set ℕ :=
  {m | ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq V)
    (G : Multigraph V E), G.indecomposable ∧ G.maxDegree G.multiplicity = r ∧ G.edges = m}

/-- The proposed least count, with `none` for degrees admitting no example. -/
def minimum (r : ℕ) : Option ℕ :=
  match r with
  | 0 => some 0
  | 1 => some 1
  | 2 => some 3
  | k + 3 => if Odd (k + 3) then some ((k + 2) * (3 * (k + 3) + 1) / 2) else none

theorem main : ∀ r : ℕ,
    match minimum r with
    | some m => IsLeast (counts r) m
    | none => counts r = ∅ := by
  sorry

end OMA.S_mo_488874
