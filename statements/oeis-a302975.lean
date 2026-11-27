import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Rat.Defs

/-!
# Square denominators of powers of the divisor count

Source: https://oeis.org/A302975 (Jaroslav Krizek, OEIS Foundation, CC BY-SA 4.0).
The sequence records the positive denominator of τ(n)^n / n^τ(n) in lowest terms.
-/

namespace OMA.S_oeis_a302975

def tau (n : ℕ) : ℕ := n.divisors.card

def a (n : ℕ) : ℕ := (((tau n : ℕ) : ℚ)^n / (n : ℚ)^tau n).den

theorem main : ∀ n : ℕ, 0 < n → ∃ m : ℕ, a n = m^2 := by
  sorry

end OMA.S_oeis_a302975
