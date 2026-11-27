import Mathlib

/-!
# Is the number $\sum_{p\text{ prime}}p^{-2}$ known to be irrational?

Source: https://mathoverflow.net/questions/242286
Credit: @nokiexow

The sum ranges over the positive primes, each occurring once.
-/

namespace OMA.S_mo_242286

theorem main : Irrational (∑' p : {n : ℕ // n.Prime}, 1 / ((p.val : ℝ) ^ 2)) := by
  sorry

end OMA.S_mo_242286

