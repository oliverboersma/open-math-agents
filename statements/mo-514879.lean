import Mathlib

/-!
# Degree of a polynomial defined by a product over all sign choices

Source: https://mathoverflow.net/questions/514879
Credit: @rleshner

Write the odd integer as `2 * k + 1` and put `x = t^(2*k+1)`.
Indexing by the roots of unity lists exactly the powers of a primitive root in the question.
A subset selects the negative signs. The outer polynomial variable is `x`, and its
coefficients are polynomials in `y`. The identity holds for every choice of square roots.
-/

namespace OMA.S_mo_514879
open Polynomial Finset

noncomputable section

local instance (n : ℕ) [NeZero n] : Fintype (rootsOfUnity n ℂ) := Fintype.ofFinite _

theorem main : ∀ k : ℕ, ∃ F : Polynomial (Polynomial ℂ),
    F.natDegree = (2 * k).choose k ∧
    ∀ (t y : ℂ) (r : rootsOfUnity (2 * k + 1) ℂ → ℂ),
      (∀ i, r i ^ 2 = t ^ 2 - (i.val : ℂ)) →
      F.eval₂ (evalRingHom y) (t ^ (2 * k + 1)) =
        ∏ s : Finset (rootsOfUnity (2 * k + 1) ℂ),
          (y - ∏ i, if i ∈ s then t - r i else t + r i) := by
  sorry

end
end OMA.S_mo_514879
