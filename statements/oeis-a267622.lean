import Mathlib

/-!
# A267622: Binary representation of the n-th iteration of the "Rule 187" elementary
cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267622
Credit: @ddanila

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
The OEIS title says "binary representation", but its Mathematica program uses
FromDigits with default base 10: bits are written as decimal digits.
Offset 0 starts with the single ON cell at position 0 on an infinite OFF background.
Standard Wolfram orientation: left bit has weight 4, centre 2, right 1.
At time n, read positions -n through n inclusive, left to right. This is the
Table/Take crop in the published Mathematica program, not all ON cells: Rule 187
turns the infinite OFF background ON at time 1.
The two conjuncts are exactly the source recurrence (n > 2) and generating function.
The denominator has constant coefficient 1; the product identity expresses the
formal quotient without introducing analytic convergence or division ambiguity.
-/
namespace OMA.S_oeis_a267622

abbrev Row := ℤ → Bool

def bit (b : Bool) : ℕ := if b then 1 else 0

def rule (l c r : Bool) : Bool :=
  decide ((187 / 2 ^ (4 * bit l + 2 * bit c + bit r)) % 2 = 1)

def step (g : Row) : Row := fun x => rule (g (x-1)) (g x) (g (x+1))

def initial : Row := fun x => decide (x = 0)

def state : ℕ → Row
  | 0 => initial
  | n+1 => step (state n)

/-- Encode m cells starting at left; the leftmost cell is most significant. -/
def encode (g : Row) (left : ℤ) : ℕ → ℕ
  | 0 => 0
  | m+1 => 10 * encode g left m + bit (g (left + (m : ℤ)))

def a (n : ℕ) : ℕ := encode (state n) (-(n : ℤ)) (2*n+1)

def series : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))

theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 101 * (a (n-1) : ℤ) - 100 * (a (n-2) : ℤ)) ∧
    (series * ((1 - PowerSeries.X) * (1 - 100 * PowerSeries.X)) =
      1 + 10 * PowerSeries.X^2) := by sorry

end OMA.S_oeis_a267622
