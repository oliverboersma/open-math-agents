import Mathlib

/-!
# Erdős Problem 289

Source: https://www.erdosproblems.com/289
Credit: @mattdorman

The source asks: is it true that, for all sufficiently large `k`, there exist finite intervals
`I₁, …, I_k ⊂ ℕ`, distinct, not overlapping or adjacent, with `|Iᵢ| ≥ 2` for `1 ≤ i ≤ k`, such that
`1 = ∑_{i=1}^{k} ∑_{n ∈ Iᵢ} 1/n`?

Reading used here: the interval `Iᵢ` is `[a i, b i]` with `1 ≤ a i` (the reciprocals are of
positive integers) and `a i < b i` (so `|Iᵢ| ≥ 2`). Two intervals neither overlap nor are adjacent
exactly when one ends at least two before the other starts, i.e. `b i + 1 < a j` or
`b j + 1 < a i`; this also makes them distinct. The statement below is the affirmative answer.
-/

open Filter

namespace OMA.S_erdos_289

theorem main :
    ∀ᶠ k : ℕ in atTop, ∃ a b : Fin k → ℕ,
      (∀ i, 1 ≤ a i ∧ a i < b i) ∧
      (∀ i j, i ≠ j → b i + 1 < a j ∨ b j + 1 < a i) ∧
      ∑ i, ∑ n ∈ Finset.Icc (a i) (b i), (1 / (n : ℚ)) = 1 := by
  sorry

end OMA.S_erdos_289
