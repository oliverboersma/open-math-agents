import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Recurrence and continued fraction for OEIS A048625

Source: https://oeis.org/A048625/internal
Harvey P. Dale conjectured the recurrence. Sergei N. Gladkovskii conjectured the continued fraction.
The rounding convention is ceiling after subtracting one half, as in the source programs.
The continued-fraction tails have constant term one, so their defining equation is cleared
of denominators and the division by the final power of X is expressed by multiplication.
-/

namespace OMA.S_oeis_a048625

noncomputable def a : ℕ → ℤ
  | 0 => 4
  | 1 => 6
  | n + 2 => ⌈(a (n + 1) : ℚ) ^ 2 / (a n : ℚ) - 1 / 2⌉

open PowerSeries

noncomputable def TailFamily (Q : ℕ → ℚ⟦X⟧) : Prop :=
  ∀ k : ℕ,
    constantCoeff (Q k) = 1 ∧
      Q k * Q (k + 1) =
        (1 + X ^ 3 + C (2 * (k : ℚ) + 3) * X) * Q (k + 1) -
          X * (C (2 * (k : ℚ) + 1) + X ^ 2)

theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = a (n - 1) + a (n - 3)) ∧
    ∃ Q : ℕ → ℚ⟦X⟧, TailFamily Q ∧ (∀ R, TailFamily R → R = Q) ∧
      X ^ 6 * PowerSeries.mk (fun n => (a n : ℚ)) =
        (1 / 2 : ℚ) • (Q 0 - 1) - (X + X ^ 2 + X ^ 3 + 2 * X ^ 4 + 3 * X ^ 5) := by
  sorry

end OMA.S_oeis_a048625
