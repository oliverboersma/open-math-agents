import Mathlib

/-!
# A283508: Binary representation of the x-axis, from the origin to the right edge,
of the n-th stage of growth of the two-dimensional cellular automaton

Source: https://oeis.org/A283508
Credit: @ddanila

OEIS A283508, https://oeis.org/A283508/internal, retrieved 2026-11-27.
OEIS Foundation and contributors; CC BY-SA 4.0.
Conventions from https://oeis.org/A283508/internal (name, comments, and program):
* Offset 0: the single ON origin is stage zero; all other initial cells are OFF.
* Every cell updates simultaneously, including the initially OFF infinite background.
* The Rule 643 program selects zero-based bit centre + 2 * orthogonal-neighbour count.
* The right edge is position n in the stage-n crop; read (0,0) through (n,0).
* FromDigits[...,10] writes cell bits as decimal digits, with the origin most significant.
* The linked Rule 641 diagrams conflict with the entry's Rule 643 program and terms;
  this statement follows the entry and program.
* The program uses a finite cyclic grid; the infinite model agrees on its published crop.

Conventions from https://oeis.org/A267623/internal:
* Use the primary middle-column description: read the centre at times 0 through n.
* Use standard Wolfram Rule 187 (left weight 4, centre 2, right 1), as in Mathematica.
  The Maple program mirrors left and right; reflection preserves this centre observation.
* Both programs write those time-ordered bits as decimal digits, starting at offset 0.
* The secondary Rule 643 comment reads left edge to origin, conflicting with its terms;
  it is not used to define A267623.

The generating-function denominator has constant coefficient 1, so it is a unit;
the product identity expresses the source's formal quotient without division.
The closed formula uses natural-number arithmetic; the recurrence is stated over integers.
-/
namespace OMA.S_oeis_a283508

abbrev Grid := ℤ → ℤ → Bool

def bit (b : Bool) : ℕ := if b then 1 else 0

def rule (c : Bool) (k : ℕ) : Bool :=
  decide ((643 / 2 ^ (bit c + 2 * k)) % 2 = 1)

def neighbors (g : Grid) (x y : ℤ) : ℕ :=
  bit (g (x+1) y) + bit (g (x-1) y) + bit (g x (y+1)) + bit (g x (y-1))

def step (g : Grid) : Grid := fun x y => rule (g x y) (neighbors g x y)

def initial : Grid := fun x y => decide (x = 0 ∧ y = 0)

def evolve (g : Grid) : ℕ → Grid
  | 0 => g
  | n+1 => step (evolve g n)

def state (n : ℕ) : Grid := evolve initial n

/-- Decimal encoding of positions 0 through m, most significant digit first. -/
def encode (g : Grid) : ℕ → ℕ
  | 0 => bit (g 0 0)
  | m+1 => 10 * encode g m + bit (g (↑(m+1 : ℕ)) 0)

def a (n : ℕ) : ℕ := encode (state n) n


namespace A267623
abbrev Row := ℤ → Bool
def rule (l c r : Bool) : Bool :=
  decide ((187 / 2 ^ (4 * bit l + 2 * bit c + bit r)) % 2 = 1)
def step (g : Row) : Row := fun x => rule (g (x-1)) (g x) (g (x+1))
def initial : Row := fun x => decide (x = 0)
def state : ℕ → Row
  | 0 => initial
  | n+1 => step (state n)
def a : ℕ → ℕ
  | 0 => bit (state 0 0)
  | n+1 => 10 * a n + bit (state (n+1) 0)

end A267623

def series : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))

theorem main :
  (series * ((1 - PowerSeries.X) * (1 - 10 * PowerSeries.X)) =
    1 - PowerSeries.X + PowerSeries.X^2) ∧
  (∀ n : ℕ, 0 < n → a n = (91 * 10^n - 10) / 90) ∧
  (∀ n : ℕ, 2 < n → (a n : ℤ) = 11 * (a (n-1) : ℤ) - 10 * (a (n-2) : ℤ)) ∧
  (∀ n : ℕ, a n = A267623.a n) := by sorry

end OMA.S_oeis_a283508
