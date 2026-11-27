import Mathlib

/-!
# OEIS A036447 — double and reverse digits

Vaclav Kotesovec conjectured that the nth roots of this sequence converge to
the square root of 10.

Source: https://oeis.org/A036447
Credit: @gblacher2
-/

namespace OMA.S_oeis_a036447

/-- Start at 1, then double the previous term and reverse its decimal digits. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.ofDigits 10 (Nat.digits 10 (2 * a n)).reverse

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ)))
      Filter.atTop (nhds (Real.sqrt 10)) := by
  sorry

end OMA.S_oeis_a036447
