import Mathlib.Algebra.Ring.Parity

/-!
# OEIS A265284

Robert Price counts all black cells from generation zero through generation n
of elementary cellular automaton Rule 94, starting with one black cell.
Colin Barker conjectured three closed formulas, a recurrence and a generating
function in 2015 and 2019.

Source: https://oeis.org/A265284
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a265284

/-- Rule 94 (binary 01011110) turns on precisely 001, 010, 011, 100 and 110. -/
def rule94 (left center right : Bool) : Bool :=
  (left != right) || (!left && center && !right)

def scan (left center : Bool) : List Bool → List Bool
  | [] => []
  | right :: tail => rule94 left center right :: scan center right tail

/-- One update of the finite row; the infinite exterior is off. -/
def next (row : List Bool) : List Bool := scan false false (row ++ [false,false])

def row : Nat → List Bool
  | 0 => [true]
  | n+1 => next (row n)

def ones : List Bool → Int
  | [] => 0
  | b :: tail => (if b then 1 else 0) + ones tail

def a : Nat → Int
  | 0 => ones (row 0)
  | n+1 => a n + ones (row (n+1))

/-- Coefficients after multiplying by (1−x)³(1+x) = 1−2x+2x³−x⁴. -/
def productCoeff : Nat → Int
  | 0 => a 0
  | 1 => a 1 - 2*a 0
  | 2 => a 2 - 2*a 1
  | 3 => a 3 - 2*a 2 + 2*a 0
  | n+4 => a (n+4) - 2*a (n+3) + 2*a (n+1) - a n

def numeratorCoeff : Nat → Int
  | 0 => 1
  | 1 => 2
  | 4 => -1
  | _ => 0

theorem main :
    (∀ n : Nat, 0 < n → 4*a n = 2*(n:Int)^2 + 12*n - (-1)^n + 1) ∧
    (∀ n : Nat, 1 < n → Even n → 2*a n = (n:Int)^2 + 6*n) ∧
    (∀ n : Nat, Odd n → 2*a n = (n:Int)^2 + 6*n + 1) ∧
    (∀ n : Nat, 4 < n → a n = 2*a (n-1) - 2*a (n-3) + a (n-4)) ∧
    (∀ n : Nat, productCoeff n = numeratorCoeff n) := by
  sorry

end OMA.S_oeis_a265284
