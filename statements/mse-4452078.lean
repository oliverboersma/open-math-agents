import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Can the derivative divided by the square of a growing function tend to infinity?

Source: Mathematics Stack Exchange question 4452078, posed by user1058535,
16 May 2022.
https://math.stackexchange.com/questions/4452078/is-there-any-function-such-that-the-limit-of-its-derivative-divided-by-its-value

This states the source's existence question for D_2. A disproof also rules out
a single function for which D_n tends to positive infinity for every positive
integer n, by specializing to n = 2.

Increasing in magnitude is interpreted as nondecreasing absolute value.
No positivity or nonvanishing assumption is added. Differentiability is
required only beyond a real threshold, exactly as in the source.
The source question text is CC BY-SA 4.0; this is a mathematical translation.
-/

namespace OMA.S_mse_4452078

theorem main :
    ∃ (f : ℝ → ℝ) (x₀ : ℝ),
      (∀ x : ℝ, x₀ < x → DifferentiableAt ℝ f x) ∧
      Monotone (fun x : ℝ => |f x|) ∧
      Filter.Tendsto (fun x : ℝ => deriv f x / (f x) ^ 2)
        Filter.atTop Filter.atTop := by
  sorry

end OMA.S_mse_4452078
