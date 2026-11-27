import Mathlib

/-!
# A267921: Decimal representation of the n-th iteration of the "Rule 243" elementary
cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267921
Credit: @ddanila

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
The source Mathematica program reads the crop [-n,n] from left to right.
FromDigits explicitly uses base 2: the displayed bits are evaluated as a binary integer.
Offset 0 starts with a single ON cell at the origin on an infinite OFF background.
Standard Wolfram orientation: left weight 4, centre 2, right 1. Rule 243 turns
the infinite OFF background ON at time 1; the crop is not the whole ON population.
The two conjuncts are exactly the source recurrence (n > 2) and generating function.
The denominator has constant coefficient 1; the product identity expresses the
formal quotient without introducing analytic convergence or division ambiguity.
-/
namespace OMA.S_oeis_a267921

abbrev Row := ℤ → Bool

def bit (b : Bool) : ℕ := if b then 1 else 0

def rule (l c r : Bool) : Bool :=
  decide ((243 / 2 ^ (4 * bit l + 2 * bit c + bit r)) % 2 = 1)

def step (g : Row) : Row := fun x => rule (g (x-1)) (g x) (g (x+1))

def initial : Row := fun x => decide (x = 0)

def state : ℕ → Row
  | 0 => initial
  | n+1 => step (state n)

/-- Encode m cells starting at left; the leftmost cell is most significant. -/
def encode (g : Row) (left : ℤ) : ℕ → ℕ
  | 0 => 0
  | m+1 => 2 * encode g left m + bit (g (left + (m : ℤ)))

def a (n : ℕ) : ℕ := encode (state n) (-(n : ℤ)) (2*n+1)

def series : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))

theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 5 * (a (n-1) : ℤ) - 4 * (a (n-2) : ℤ)) ∧
    (series * ((1 - PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
      1 + 8 * PowerSeries.X^2) := by sorry

end OMA.S_oeis_a267921
