import Mathlib

/-!
# Hardin's two-column triangular graph arrays (OEIS A223299)

Hardin's graph has ten vertices. Each row is an oriented edge, and both
columns must follow graph edges between consecutive rows. The enumeration
starts at height one. The ordinary generating series has constant term zero.
The generating-function identity is multiplied by its denominator, whose
constant term is one. The closed form absorbs the factor 2⁻ⁿ into the roots.

Source: https://oeis.org/A223299 (R. H. Hardin, 2013; Colin Barker, 2018).
Formalization: @thomasfredrickson with Codex.
-/

namespace OMA.S_oeis_a223299
open PowerSeries

abbrev Row := ℕ × ℕ

def edges : List Row := [
  (0,1), (0,2), (1,2), (1,3), (1,4), (2,4), (3,4), (2,5), (4,5),
  (3,6), (3,7), (4,7), (6,7), (4,8), (5,8), (7,8), (5,9), (8,9)]

def rows : List Row := edges ++ edges.map Prod.swap

def after (r : Row) : List Row :=
  rows.filter fun s => rows.contains (r.1, s.1) && rows.contains (r.2, s.2)

/-- All grids with a fixed first row and exactly n further rows. -/
def grids : ℕ → Row → List (List Row)
  | 0, r => [[r]]
  | n + 1, r => (after r).flatMap fun s => (grids n s).map (r :: ·)

/-- Count all grids of positive height, using zero as the generating-series constant. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (rows.flatMap (grids n)).length

noncomputable def closedValue (n : ℕ) : ℝ :=
  let s := Real.sqrt 73
  3 / s * ((s - 1) * ((11 - s)/2)^n + (s + 1) * ((11 + s)/2)^n)

theorem main :
    (∀ n : ℕ, a (n+3) + 12 * a (n+1) = 11 * a (n+2)) ∧
    ((1 - 11 * X + 12 * X ^ 2) *
      (PowerSeries.mk (fun n => (a n : ℚ))) = 36 * X * (1 - 2 * X)) ∧
    ∀ n : ℕ, (a (n+1) : ℝ) = closedValue (n+1) := by
  sorry

end OMA.S_oeis_a223299
