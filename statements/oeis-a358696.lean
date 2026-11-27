import Mathlib

/-!
Seiichi Manyama's 2022 conjecture for OEIS A358696 concerns unoriented simple cycles in a five-by-n grid that use every
boundary vertex. A cycle is represented by its undirected edge set, so changing
the starting point or direction does not change the counted object.
Source: https://oeis.org/A358696
-/

namespace OMA.S_oeis_a358696

abbrev Vertex (n : ℕ) := Fin 5 × Fin n

def grid (n : ℕ) : SimpleGraph (Vertex n) :=
  (SimpleGraph.pathGraph 5).boxProd (SimpleGraph.pathGraph n)

def boundary {n : ℕ} (v : Vertex n) : Prop :=
  v.1.val = 0 ∨ v.1.val + 1 = 5 ∨ v.2.val = 0 ∨ v.2.val + 1 = n

def isBoundaryCycle {n : ℕ} (edges : Finset (Sym2 (Vertex n))) : Prop :=
  let G := SimpleGraph.fromEdgeSet (edges : Set (Sym2 (Vertex n)))
  (edges : Set (Sym2 (Vertex n))) ⊆ (grid n).edgeSet ∧
    (G.induce G.support).Connected ∧ G.IsCycles ∧
    ∀ v : Vertex n, boundary v → v ∈ G.support

noncomputable def a (n : ℕ) : ℤ :=
  (Nat.card {edges : Finset (Sym2 (Vertex n)) // isBoundaryCycle edges} : ℤ)

theorem main : ∀ n : ℕ, 11 ≤ n →
    a n = 6 * a (n - 1) + a (n - 2) - 20 * a (n - 3) + 37 * a (n - 4) +
      16 * a (n - 5) - 12 * a (n - 6) - 7 * a (n - 7) + 5 * a (n - 8) -
      a (n - 9) := by
  sorry

end OMA.S_oeis_a358696
