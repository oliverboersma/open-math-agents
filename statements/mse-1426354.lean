import Mathlib

/-!
# An explicit improvement of the Lagarias bound

The question asks for an intermediate upper bound between the divisor sum and
the Lagarias expression. We propose the latter up to 5040, then drop its
additive harmonic-number term. The integral expression in the question equals
the Lagarias expression by integration by parts.

Source: https://math.stackexchange.com/q/1426354 (user243301, CC BY-SA 3.0)
Formalization: @DomTheDeveloper
-/

namespace OMA.S_mse_1426354

noncomputable def tailTerm (n : ℕ) : ℝ :=
  Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

noncomputable def upperBound (n : ℕ) : ℝ :=
  if n ≤ 5040 then (harmonic n : ℝ) + tailTerm n else tailTerm n

theorem main : ∀ n : ℕ, 1 ≤ n →
    (ArithmeticFunction.sigma 1 n : ℝ) ≤ upperBound n ∧
    upperBound n ≤ (harmonic n : ℝ) + tailTerm n ∧
    (5040 < n → upperBound n < (harmonic n : ℝ) + tailTerm n) := by
  sorry

end OMA.S_mse_1426354
