import Mathlib

/-!
# Erdős-Posa property for long directed cycles

Source: https://www.openproblemgarden.org/op/erdos_posa_property_for_long_directed_cycles
Credit: @LAPRAI

Conjecture: let `ℓ ≥ 2` be an integer. For every integer `n ≥ 0`, there exists an integer
`t_n = t_n(ℓ)` such that for every digraph `D`, either `D` has `n` pairwise-disjoint directed
cycles of length at least `ℓ`, or there exists a set `T` of at most `t_n` vertices such that
`D - T` has no directed cycles of length at least `ℓ`.

## Encoding

* Digraphs are finite Mathlib `Digraph`s (a loop would be a cycle of length `1 < ℓ`, so loops are
  irrelevant).
* A directed cycle of length `m` is an injective sequence `c 0, …, c (m-1)` with an arc from each
  `c i` to `c (i + 1 mod m)`; its vertex set is the range of `c`.
* *Pairwise-disjoint*: the vertex sets of the `n` cycles are pairwise disjoint.
* *`D - T` has no directed cycle of length at least `ℓ`*: every directed cycle of `D` of length
  at least `ℓ` meets `T`.
-/

namespace OMA.S_opg_erdos_posa_property_for_long_directed_cycles

/-- `c` is a directed cycle of `D` (of length `m`). -/
def IsDirectedCycle {V : Type} (D : Digraph V) {m : ℕ} (c : Fin m → V) : Prop :=
  Function.Injective c ∧ ∀ i : Fin m, D.Adj (c i) (c (finRotate m i))

/-- **Erdős–Pósa property for directed cycles of length at least `ℓ`.** -/
theorem main : ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ n : ℕ, ∃ t : ℕ, ∀ (V : Type) [Fintype V] (D : Digraph V),
    (∃ (len : Fin n → ℕ) (C : (j : Fin n) → Fin (len j) → V),
        (∀ j, ℓ ≤ len j ∧ IsDirectedCycle D (C j)) ∧
        ∀ i j, i ≠ j → Disjoint (Set.range (C i)) (Set.range (C j))) ∨
    (∃ T : Finset V, T.card ≤ t ∧ ∀ (m : ℕ) (c : Fin m → V), ℓ ≤ m → IsDirectedCycle D c →
        ∃ i, c i ∈ T) := by
  sorry

end OMA.S_opg_erdos_posa_property_for_long_directed_cycles
