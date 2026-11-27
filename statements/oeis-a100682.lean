import Mathlib.Data.Nat.Sqrt

/-!
# Fourth roots of pentatope numbers

The OEIS entry numbers its terms from zero and defines the nth pentatope
number as n(n+1)(n+2)(n+3)/24. For an integer m, taking the integer square
root twice gives the floor of the fourth root. At every index under
consideration n is at least 2. Raising the positive quantity
(n-3/2)/24^(1/4) to the fourth power gives (2n-3)^4/384. Taking the integer
part of this rational before the two square roots preserves its fourth-root
floor. Thus both real floors in the conjecture have exact integer formulas.

Source: https://oeis.org/A100682 (conjecture by Charles R. Greathouse IV)
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a100682

def fourthRoot (m : ℕ) := Nat.sqrt (Nat.sqrt m)

def pentatope (n : ℕ) := n * (n+1) * (n+2) * (n+3) / 24

def estimate (n : ℕ) := fourthRoot ((2*n-3)^4 / 384)

theorem main : ∀ n : ℕ, n ∉ [0, 1, 6, 17, 2403, 5318] →
    fourthRoot (pentatope n) = estimate n := by
  sorry

end OMA.S_oeis_a100682
