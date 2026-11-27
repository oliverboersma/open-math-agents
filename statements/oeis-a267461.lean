import Mathlib

/-!
# OEIS A267461: Barker's conjectures for the OFF cells of Rule 133

Source: https://oeis.org/A267461 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267461 (Robert Price, Jan 15 2016), offset 0: Total number of OFF (white) cells after n
iterations of the Rule 133 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 16 2016:
a(n) = (2*n^2+12*n-(-1)^n-7)/4 for n>0.
a(n) = 2*a(n-1) - 2*a(n-3) + a(n-4) for n>4.
G.f.: 2*x*(1+x-x^3) / ((1-x)^3*(1+x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 133 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: as in the entry's program, stage t counts the OFF cells among the cells
  -t..t, and a(n) is the sum of these counts for t = 0..n.
* The statement is the conjunction of the three conjectures. The closed form is stated for n > 0
  as 4a(n) = 2n^2+12n-(-1)^n-7 in the integers, and the recurrence in the integers. Since the
  denominator of the generating function has constant term 1, the identity A(x) = N/D for
  A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the formal power series ring over the
  integers.
* Controls from the entry: the definition gives 0, 2, 6, 12, 18, 26, 34, 44, 54, 66, 78, 92 for
  n = 0..11.
-/

namespace OMA.S_oeis_a267461

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 133 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 133 (state t (i - 1)) (state t i) (state t (i + 1))

/-- The number of OFF cells of stage t among the cells -t..t. -/
def white (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun k : ℕ => state t ((k : ℤ) - (t : ℤ)) = false).card

/-- A267461(n): the total number of OFF cells in stages 0..n. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), white t

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 0 < n → 4 * (a n : ℤ) = 2 * (n : ℤ) ^ 2 + 12 * n - (-1) ^ n - 7) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X)) =
      (2 * X * (1 + X - X ^ 3) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a267461
