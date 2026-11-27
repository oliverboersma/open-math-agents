import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A lower bound for the parity sum of powers of four thirds

For positive `k`, natural-number division `4^k / 3^k` gives the exact
floor of `(4/3)^k`. Each odd floor contributes `+1`, and each even floor
contributes `-1`. The recurrence starts with the empty sum at zero, so
`a n` includes the terms indexed from one through `n`.

Source: https://oeis.org/A071622 (Benoit Cloitre)
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a071622

def contribution (k : ℕ) : ℤ := if (4 ^ k / 3 ^ k : ℕ) % 2 = 0 then -1 else 1

def a : ℕ → ℤ
  | 0 => 0
  | k + 1 => a k + contribution (k + 1)

theorem main : ∀ n : ℕ, 2300 < n → (Real.log (n : ℝ)) ^ 2 < (a n : ℝ) := by
  sorry

end OMA.S_oeis_a071622
