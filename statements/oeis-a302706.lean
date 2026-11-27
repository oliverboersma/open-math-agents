import Mathlib

/-!
# OEIS A302706: maximal remainders of sums of two squares

Source: https://oeis.org/A302706
Conjecture: Andres Cicuttin, October 18, 2018.
Credit: @caa1982
-/

open Filter
open scoped Topology

namespace OMA.S_oeis_a302706

/-- The pairs of positive integers with `x ≤ y ≤ n`. -/
def pairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p => p.1 ≤ p.2

/-- A302706 for `n ≥ 1`, extended by zero at `n = 0`. -/
def a (n : ℕ) : ℕ :=
  (pairs n).sup fun p => (p.1 ^ 2 + p.2 ^ 2) % (p.1 + p.2)

/-- The normalized maximum tends to one, and maximizing pairs can be chosen
with both coordinates asymptotic to `n`. Values at `n = 0` do not affect the limits. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / (2 * (n : ℝ))) atTop (𝓝 1) ∧
    ∃ x y : ℕ → ℕ,
      (∀ᶠ n in atTop, 0 < x n ∧ x n ≤ y n ∧ y n ≤ n ∧
        (x n ^ 2 + y n ^ 2) % (x n + y n) = a n) ∧
      Tendsto (fun n : ℕ => (x n : ℝ) / (n : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => (y n : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a302706
