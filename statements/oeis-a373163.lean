import Mathlib

/-!
# A373163 and complete monotonicity

The conjecture concerns the fractions themselves. The OEIS entry records
their numerators. For the forward difference Δf(n) = f(n+1) − f(n), complete
monotonicity means (−1)^k Δ^k f(n) ≥ 0 at every order and index.

Source: https://oeis.org/A373163
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a373163

/-- The cosine series giving the fractions, defined on their OEIS domain n ≥ 2. -/
noncomputable def fraction (n : ℕ) : ℝ :=
  ∑' k : ℕ, Real.cos (2*k*Real.pi/3) / (n:ℝ)^k

theorem main : ∀ k n : ℕ, 2 ≤ n →
    0 ≤ (-1:ℝ)^k * (fwdDiff 1)^[k] fraction n := by
  sorry

end OMA.S_oeis_a373163
