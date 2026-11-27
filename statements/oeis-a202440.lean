import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Int.Defs

/-!
# OEIS A202440

R. H. Hardin counts (n+2)-by-3 binary arrays avoiding 001 and 110 from
left to right, top to bottom and northwest to southeast. Colin Barker
conjectured the generating function and recurrence on May 28, 2018.

Source: https://oeis.org/A202440
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a202440

/-- Bits are numbered from the left-hand edge of a row. -/
def bit (w j : Nat) : Bool := w.testBit j

/-- A triple avoids 001 and 110 exactly when equal first and second bits
force the third to be equal as well. -/
def allowed (x y z : Bool) : Bool := (x != y) || (y == z)

def rowOK (w : Nat) : Bool := allowed (bit w 0) (bit w 1) (bit w 2)

/-- Append row c below the two rows stored in s. Check the new row,
three vertical triples and the unique northwest-to-southeast triple. -/
def compatible (s : Fin 64) (c : Fin 8) : Bool :=
  let u := s.val / 8
  let v := s.val % 8
  rowOK u && rowOK v && rowOK c.val &&
    allowed (bit u 0) (bit v 0) (bit c.val 0) &&
    allowed (bit u 1) (bit v 1) (bit c.val 1) &&
    allowed (bit u 2) (bit v 2) (bit c.val 2) &&
    allowed (bit u 0) (bit v 1) (bit c.val 2)

def targets (s : Fin 64) : Finset (Fin 8) :=
  Finset.univ.filter (fun c => compatible s c = true)

def nextPair (s : Fin 64) (c : Fin 8) : Fin 64 :=
  ⟨(8 * s.val + c.val) % 64, Nat.mod_lt _ (by decide)⟩

def step (f : Fin 64 → Int) (s : Fin 64) : Int :=
  ∑ c ∈ targets s, f (nextPair s c)

/-- The number of ways to append n rows to a particular initial pair. -/
def count : Nat → Fin 64 → Int
  | 0, s => if rowOK (s.val / 8) && rowOK (s.val % 8) then 1 else 0
  | n + 1, s => step (count n) s

def total (n : Nat) : Int := ∑ s : Fin 64, count n s

/-- The OEIS sequence starts at one. Its generating series has zero
constant coefficient. -/
def a : Nat → Int
  | 0 => 0
  | n + 1 => total (n + 1)

def fourth (f : Nat → Int) : Int := f 4 - 4*f 3 + 6*f 2 - 4*f 1 + f 0

/-- Coefficients after multiplying the ordinary generating series by (1-x)^4. -/
def productCoeff : Nat → Int
  | 0 => a 0
  | 1 => a 1 - 4*a 0
  | 2 => a 2 - 4*a 1 + 6*a 0
  | 3 => a 3 - 4*a 2 + 6*a 1 - 4*a 0
  | n + 4 => fourth (fun j => a (n+j))

/-- Coefficients of 2x(40-91x+76x²-25x³+2x⁴). -/
def numerator : Nat → Int
  | 1 => 80
  | 2 => -182
  | 3 => 152
  | 4 => -50
  | 5 => 4
  | _ => 0

theorem main :
    (∀ n : Nat, fourth (fun j => a (n+(j+2))) = 0) ∧
    (∀ n : Nat, productCoeff n = numerator n) := by
  sorry

end OMA.S_oeis_a202440
