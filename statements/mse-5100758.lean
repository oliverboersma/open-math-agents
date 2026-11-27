import Mathlib

/-!
# Is it true that the sequence $\{n \sin(n^n/2)\}$ is unbounded but doesn't tend to infinity?

Source: https://math.stackexchange.com/questions/5100758/is-it-true-that-the-sequence-n-sinnn-2-is-unbounded-but-doesnt-tend-t
Credit: @mgv27

Is it true that the sequence $\{n \sin(n^n/2)\}$ is unbounded but does not tend to infinity?
Here "a sequence $\{a_n\}$ tends to infinity" means $\lim_{n\to\infty} |a_n| = +\infty$.
(The asker can handle $\{n \sin n\}$ via Dirichlet approximation and density of $\{\sin n\}$,
but cannot adapt the argument to $n^n/2$; even density of $\{n^n \alpha\}$ mod 1 is unclear.)

Formalization notes:
* `a n = n * sin(n^n / 2)` with `n^n` computed in `ℕ` and cast to `ℝ` (the sine argument is
  in radians).
* `main` asserts both parts: `a` is unbounded (no `C` with `|a n| ≤ C` for all `n`), and
  `|a n|` does not tend to `+∞`.
-/

namespace OMA.S_mse_5100758

open Filter

/-- The sequence `a n = n * sin(n^n / 2)`. -/
noncomputable def a (n : ℕ) : ℝ := (n : ℝ) * Real.sin (((n ^ n : ℕ) : ℝ) / 2)

/-- The sequence `n sin(n^n/2)` is unbounded, but `|n sin(n^n/2)|` does not tend to `+∞`. -/
theorem main :
    (¬ ∃ C : ℝ, ∀ n : ℕ, |a n| ≤ C) ∧ ¬ Tendsto (fun n : ℕ => |a n|) atTop atTop := by
  sorry

end OMA.S_mse_5100758
