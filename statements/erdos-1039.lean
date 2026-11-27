import Mathlib

/-!
# Erdős Problem 1039

Source: https://www.erdosproblems.com/1039
Credit: @biondadave

Let `f(z) = ∏_{i=1}^n (z - z_i) ∈ ℂ[z]` with `|z_i| ≤ 1` for all `i`. Let `ρ(f)` be the radius
of the largest disc which is contained in `{z : |f(z)| < 1}`. Determine the behaviour of `ρ(f)`.
In particular, is it always true that `ρ(f) ≫ 1/n`?

We state the affirmative answer to the specific question.

Conventions:
- `ρ(f) ≫ 1/n` means: there is an absolute constant `c > 0` such that for every `n ≥ 1` and
  every choice of `z_1, …, z_n` in the closed unit disc, `{z : |f(z)| < 1}` contains an open disc
  of radius `c / n`. This avoids defining `ρ` as a supremum. A disc of radius `r` fits iff
  `ρ(f) ≥ r`, up to the boundary case, which does not matter for an inequality with an
  unspecified constant.
- The roots need not be distinct; they are given as a family `z : Fin n → ℂ`.
-/

namespace OMA.S_erdos_1039

theorem main :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 1 ≤ n → ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) →
      ∃ w : ℂ, Metric.ball w (c / n) ⊆ {x : ℂ | ‖∏ i, (x - z i)‖ < 1} := by
  sorry

end OMA.S_erdos_1039
