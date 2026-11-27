import Mathlib

/-!
# MathOverflow 452919: spectrum of the adjacency matrix of certain directed graphs

Source: https://mathoverflow.net/questions/452919
Credit: @OrangeHeadz (agent: Claude Code, model claude-fable-5-2)

Question (F J): Suppose in a directed graph `G`, each edge is contained in a cycle (e.g.,
undirected graphs, directed cycle graphs). Is it true that each Jordan block of the adjacency
matrix `A_G` has size `1`?

We state the affirmative answer; a disproof of `main` answers the question negatively.

Conventions:
* A directed graph is a finite directed graph without parallel edges: Mathlib's `Digraph` on a
  finite vertex type `V`. Loops and pairs of opposite edges are allowed; an undirected graph is the
  case where every edge comes with its opposite.
* A cycle is a closed directed walk `v₀ → v₁ → ⋯ → v_k → v₀` with distinct vertices
  `v₀, …, v_k` (`k ≥ 0`). So the edge `u → v` is contained in a cycle iff there is a directed
  path `v = w₀ → w₁ → ⋯ → w_k = u` through distinct vertices; the edge `u → v` closes it.
  Here `k = 0` is a loop and `k = 1` is a pair of opposite edges.
* `A_G` is the `V × V` matrix over `ℂ` whose `(u, v)` entry is `1` if `u → v` and `0` otherwise.
* Every Jordan block of `A_G` has size `1` iff the Jordan normal form of `A_G` over `ℂ` is
  diagonal, i.e. iff `A_G` is similar to a diagonal matrix: `A_G * P = P * D` for some invertible
  `P` and some diagonal `D`.
-/

namespace OMA.S_mo_452919

/-- The edge `u → v` of `G` is contained in a cycle: there is a directed path from `v` back to `u`
through distinct vertices (the list `p`, starting at `v` and ending at `u`). -/
def EdgeOnCycle {V : Type} (G : Digraph V) (u v : V) : Prop :=
  ∃ p : List V, p.Nodup ∧ p.IsChain G.Adj ∧ p.head? = some v ∧ p.getLast? = some u

/-- The adjacency matrix of `G` over `ℂ`. -/
noncomputable def adjMatrix {V : Type} (G : Digraph V) [DecidableRel G.Adj] : Matrix V V ℂ :=
  Matrix.of fun u v => if G.Adj u v then 1 else 0

/-- If every edge of a finite directed graph is contained in a cycle, then its adjacency matrix is
diagonalizable over `ℂ`, i.e. every Jordan block has size `1`. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
    (∀ u v : V, G.Adj u v → EdgeOnCycle G u v) →
    ∃ (P : Matrix V V ℂ) (d : V → ℂ),
      IsUnit P.det ∧ adjMatrix G * P = P * Matrix.diagonal d := by
  sorry

end OMA.S_mo_452919
