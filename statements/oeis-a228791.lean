import Mathlib.Analysis.Real.Sqrt

/-!
# OEIS A228791

R. H. Hardin counts n-by-3 binary arrays with a one in the top left
corner and no two ones adjacent horizontally or northwest-to-southeast.
Colin Barker conjectured a generating function and a radical formula
for the resulting sequence on September 13, 2018.

Source: https://oeis.org/A228791
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a228791

/-- The five possible last rows, named by the positions of their ones. -/
structure Rows where
  empty : Int
  left : Int
  middle : Int
  right : Int
  outer : Int

def Rows.total (v : Rows) : Int :=
  v.empty + v.left + v.middle + v.right + v.outer

/-- A one in the new middle column forbids a one above left.
A one in the new right column forbids a one above middle.
There is no upper-left neighbor for the new left column. -/
def extend (v : Rows) : Rows :=
  ⟨v.total, v.total, v.empty + v.middle + v.right,
    v.empty + v.left + v.right + v.outer, v.empty + v.left + v.right + v.outer⟩

/-- Counts after n+1 rows. The top-left one allows the first row 100 or 101. -/
def state : Nat → Rows
  | 0 => ⟨0, 1, 0, 0, 1⟩
  | n + 1 => extend (state n)

def a : Nat → Int
  | 0 => 0
  | n + 1 => (state n).total

/-- Coefficients of (1−5x+3x²) times the generating series. -/
def productCoeff : Nat → Int
  | 0 => a 0
  | 1 => a 1 - 5 * a 0
  | n + 2 => a (n + 2) - 5 * a (n + 1) + 3 * a n

/-- Coefficients of 2x(1−x+x²). -/
def numeratorCoeff : Nat → Int
  | 1 => 2
  | 2 => -2
  | 3 => 2
  | _ => 0

/-- The factor 2^(1−n) in the source is written 2/2^n. -/
noncomputable def closedForm (n : Nat) : ℝ :=
  -((2 / (2 : ℝ)^n) * ((-11 + Real.sqrt 13) * (5 + Real.sqrt 13)^n +
    (5 - Real.sqrt 13)^n * (11 + Real.sqrt 13))) / (9 * Real.sqrt 13)

theorem main :
    (∀ n : Nat, productCoeff n = numeratorCoeff n) ∧
    (∀ n : Nat, 1 < n → (a n : ℝ) = closedForm n) := by
  sorry

end OMA.S_oeis_a228791
