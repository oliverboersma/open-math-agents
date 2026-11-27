import Mathlib

/-!
# Erdős Problem 176

Source: https://www.erdosproblems.com/176
Credit: @biondadave

Let `N(k, ℓ)` be the minimal `N` such that for any `f : {1, …, N} → {-1, 1}` there must exist a
`k`-term arithmetic progression `P` such that `|∑_{n ∈ P} f(n)| ≥ ℓ`. Find good upper bounds for
`N(k, ℓ)`. Is it true that for any `c > 0` there exists some `C > 1` such that
`N(k, ck) ≤ C^k`?

We state the affirmative answer to this question. The follow-up questions on the source page
(`N(k, 2) ≤ C^k`, `N(k, √k) ≤ C^k`) are not stated here.

Conventions:
- `c` ranges over `0 < c < 1`. For `c > 1` no `k`-term progression can have
  `|∑ f| ≥ ck > k`, so `N(k, ck)` does not exist and the question is only meaningful for
  `c ≤ 1`. At `c = 1` it asks about the van der Waerden number `W(k) = N(k, k)`, which the
  source treats as a separate problem ([138]).
- A `k`-term arithmetic progression in `{1, …, N}` is `a, a + d, …, a + (k - 1) d` with `a ≥ 1`,
  common difference `d ≥ 1` and `a + (k - 1) d ≤ N`.
- `N(k, ℓ) ≤ C^k` is stated as: every `N ≥ C^k` has the property. The property is monotone in
  `N`, so this agrees with the source up to rounding `C^k` to an integer, which the existential
  `C` absorbs.
- `f` is given on all of `ℕ`; only its values on `{1, …, N}` matter.
-/

namespace OMA.S_erdos_176

theorem main :
    ∀ c : ℝ, 0 < c → c < 1 → ∃ C : ℝ, 1 < C ∧ ∀ k : ℕ, 1 ≤ k → ∀ N : ℕ, C ^ k ≤ N →
      ∀ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) →
        ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ a + (k - 1) * d ≤ N ∧
          c * k ≤ |((∑ i ∈ Finset.range k, f (a + i * d) : ℤ) : ℝ)| := by
  sorry

end OMA.S_erdos_176
