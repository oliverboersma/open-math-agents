import Mathlib.Analysis.Real.Sqrt

/-!
# OEIS A228797

R. H. Hardin counts two-row binary arrays whose top left entry is one
and whose horizontally adjacent or northwest-to-southeast adjacent
entries cannot both be one. Colin Barker conjectured a generating
function and a closed formula on September 13, 2018.

Source: https://oeis.org/A228797
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a228797

/-- Counts indexed by the last column, listed as (top bit, bottom bit). -/
structure Columns where
  bothZero : Int
  bottomOnly : Int
  topOnly : Int
  bothOne : Int

def Columns.total (v : Columns) : Int :=
  v.bothZero + v.bottomOnly + v.topOnly + v.bothOne

/-- End in 00 after any column. End in 01 or 11 only after 00 since a
bottom one conflicts with either one in the preceding column. End in 10
after 00 or 01 since a top one conflicts with a preceding top one. -/
def extend (v : Columns) : Columns :=
  ⟨v.total, v.bothZero, v.bothZero + v.bottomOnly, v.bothZero⟩

/-- Counts for n+1 columns. The first column is 10 or 11. -/
def state : Nat → Columns
  | 0 => ⟨0, 0, 1, 1⟩
  | n + 1 => extend (state n)

/-- The sequence starts at index one; the generating function has
constant coefficient zero. -/
def a : Nat → Int
  | 0 => 0
  | n + 1 => (state n).total

/-- Coefficients of (1+x)(1−2x−x²) A(x) = (1−x−3x²−x³) A(x). -/
def productCoeff : Nat → Int
  | 0 => a 0
  | 1 => a 1 - a 0
  | 2 => a 2 - a 1 - 3 * a 0
  | n + 3 => a (n + 3) - a (n + 2) - 3 * a (n + 1) - a n

noncomputable def closedForm (n : Nat) : ℝ :=
  (-2 * (-1 : ℝ) ^ n + (1 - Real.sqrt 2) ^ n + (1 + Real.sqrt 2) ^ n) / 2

theorem main :
    (∀ n : Nat, productCoeff n = (if n = 1 then 2 else 0)) ∧
    (∀ n : Nat, 1 ≤ n → (a n : ℝ) = closedForm n) := by
  sorry

end OMA.S_oeis_a228797
