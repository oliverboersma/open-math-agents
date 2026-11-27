import Mathlib

/-!
# A267623: Binary representation of the middle column of the "Rule 187"
elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267623
Credit: @ddanila

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
The OEIS title says "binary representation", but its Mathematica program uses
FromDigits with default base 10: bits are written as decimal digits.
Offset 0 starts with the single ON cell at position 0 on an infinite OFF background.
Standard Wolfram orientation: left bit has weight 4, centre 2, right 1.
At time n, read the centre cell at times 0 through n, oldest first, as decimal
digits. This is the mc/Take/FromDigits operation in the Mathematica program.
The Maple program reflects spatial orientation; reflection fixes the centre.
The two conjuncts are exactly the source recurrence (n > 2) and generating function.
The denominator has constant coefficient 1; the product identity expresses the
formal quotient without introducing analytic convergence or division ambiguity.
-/
namespace OMA.S_oeis_a267623

abbrev Row := ℤ → Bool

def bit (b : Bool) : ℕ := if b then 1 else 0

def rule (l c r : Bool) : Bool :=
  decide ((187 / 2 ^ (4 * bit l + 2 * bit c + bit r)) % 2 = 1)

def step (g : Row) : Row := fun x => rule (g (x-1)) (g x) (g (x+1))

def initial : Row := fun x => decide (x = 0)

def state : ℕ → Row
  | 0 => initial
  | n+1 => step (state n)

/-- Encode the first m centre cells chronologically as decimal digits. -/
def column : ℕ → ℕ
  | 0 => 0
  | m+1 => 10 * column m + bit (state m 0)

def a (n : ℕ) : ℕ := column (n+1)

def series : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))

theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 11 * (a (n-1) : ℤ) - 10 * (a (n-2) : ℤ)) ∧
    (series * ((1 - PowerSeries.X) * (1 - 10 * PowerSeries.X)) =
      1 - PowerSeries.X + PowerSeries.X^2) := by sorry

end OMA.S_oeis_a267623
