import Mathlib

/-!
# Hoàng-Reed Conjecture

Source: https://www.openproblemgarden.org/op/hoand_reed_conjecture
Credit: @LAPRAI

Conjecture (Hoàng–Reed): every digraph in which each vertex has outdegree at least `k` contains
`k` directed cycles `C₁, …, C_k` such that `C_j` meets `C₁ ∪ ⋯ ∪ C_{j-1}` in at most one vertex,
for `2 ≤ j ≤ k`.

## Encoding

* Digraphs are finite, nonempty Mathlib `Digraph`s without loops (opposite arcs `u → v`,
  `v → u` are allowed and form a directed cycle of length `2`). For the empty digraph the degree
  condition holds vacuously and there is no cycle, so it is excluded.
* A directed cycle of length `ℓ ≥ 2` is an injective sequence `c 0, …, c (ℓ-1)` with an arc from
  each `c i` to `c (i + 1 mod ℓ)`; its vertex set is the range of `c`.
* The cycles are indexed by `j : Fin k`; the condition for `j` (vacuous for the first cycle) is
  that the vertex set of `C_j` shares at most one vertex with the union of those of the `C_i`,
  `i < j`.
-/

namespace OMA.S_opg_hoand_reed_conjecture

/-- The outdegree of `v`. -/
def outdegree {V : Type} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w)).card

/-- `c` is a directed cycle of `G` of length `ℓ ≥ 2`. -/
def IsDirectedCycle {V : Type} (G : Digraph V) {ℓ : ℕ} (c : Fin ℓ → V) : Prop :=
  2 ≤ ℓ ∧ Function.Injective c ∧ ∀ i : Fin ℓ, G.Adj (c i) (c (finRotate ℓ i))

/-- **Hoàng–Reed conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (k : ℕ), (∀ v, ¬ G.Adj v v) → (∀ v, k ≤ outdegree G v) →
    ∃ (len : Fin k → ℕ) (C : (j : Fin k) → Fin (len j) → V),
      (∀ j, IsDirectedCycle G (C j)) ∧
      ∀ j : Fin k, (Set.range (C j) ∩ ⋃ (i : Fin k) (_ : i < j), Set.range (C i)).ncard ≤ 1 := by
  sorry

end OMA.S_opg_hoand_reed_conjecture
