import Mathlib

/-!
# Erdős Problem 788

Source: https://www.erdosproblems.com/788
Credit: @biondadave

Let `f(n)` be maximal such that if `B ⊂ (2n, 4n) ∩ ℕ` there exists some `C ⊂ (n, 2n) ∩ ℕ` such
that `c₁ + c₂ ∉ B` for all `c₁ ≠ c₂ ∈ C` and `|C| + |B| ≥ f(n)`. Estimate `f(n)`. In particular,
is it true that `f(n) ≤ n^{1/2 + o(1)}`?

We state the affirmative answer to the specific question. (`f(n) ≫ n^{1/2}` is known, and the
best upper bound is `(n log n)^{2/3}`, so this would determine `f` up to `n^{o(1)}`.)

Conventions:
- By definition `f(n) = min_B max_C (|C| + |B|)`, with `C` ranging over the admissible sets
  for `B`. Hence `f(n) ≤ X` holds iff some `B ⊆ (2n, 4n)` makes every admissible `C ⊆ (n, 2n)`
  satisfy `|C| + |B| ≤ X`. We state it in this form, without defining `f`.
- `f(n) ≤ n^{1/2 + o(1)}` means: for every `ε > 0`, for all sufficiently large `n`,
  `f(n) ≤ n^{1/2 + ε}`.
- The intervals `(2n, 4n)` and `(n, 2n)` are open, as written on the source page.
-/

namespace OMA.S_erdos_788

theorem main :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B ⊆ Finset.Ioo (2 * n) (4 * n),
        ∀ C ⊆ Finset.Ioo n (2 * n),
          (∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → c₁ + c₂ ∉ B) →
          ((C.card + B.card : ℕ) : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  sorry

end OMA.S_erdos_788
