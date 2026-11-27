import Mathlib

/-!
# OEIS A266438: De Vlieger's generating function and Barker's conjectures for Rule 23

Source: https://oeis.org/A266438 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266438 (Robert Price, Dec 29 2015), offset 0: Total number of ON (black) cells after n
iterations of the Rule 23 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectured g.f.: (-(1 + x)^(-2) + (-3 + 3*x - 2*x^2)/(-1 + x)^3)/2. - Michael De Vlieger, Dec 29
2015
Conjectures from Colin Barker, Dec 30 2015 and Apr 15 2019:
a(n) = (n^2+2*n-(-1)^n*(n+1)+3)/2.
a(n) = a(n-1)+2*a(n-2)-2*a(n-3)-a(n-4)+a(n-5) for n>4.

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 23 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: as in the entry's program, stage t counts the ON cells among the cells
  -t..t, and a(n) is the sum of these counts for t = 0..n.
* The statement is the conjunction of the three conjectures. De Vlieger's generating function
  equals (1 + 3x - 2x^2 + x^3 + x^4)/((1+x)^2 (1-x)^3), because
  -(1-x)^3 + (3 - 3x + 2x^2)(1+x)^2 = 2 + 6x - 4x^2 + 2x^3 + 2x^4; since the denominator has
  constant term 1, the identity A(x) = N/D for A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N
  in the formal power series ring over the integers. Barker's closed form, which has no stated
  range, is stated for every n >= 0 as 2a(n) = n^2+2n-(-1)^n(n+1)+3 in the integers; the
  recurrence is stated in the integers.
* Controls from the entry: the definition gives 1, 4, 4, 11, 11, 22, 22, 37, 37, 56 for n = 0..9.
-/

namespace OMA.S_oeis_a266438

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 23 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 23 (state t (i - 1)) (state t i) (state t (i + 1))

/-- The number of ON cells of stage t among the cells -t..t. -/
def black (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun i : ℕ => state t ((i : ℤ) - (t : ℤ))).card

/-- A266438(n): the total number of ON cells in stages 0..n. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), black t

/-- De Vlieger's generating function, Barker's closed form and Barker's recurrence. -/
theorem main :
    mk (fun n => (a n : ℤ)) * ((1 + X) ^ 2 * (1 - X) ^ 3) =
      (1 + 3 * X - 2 * X ^ 2 + X ^ 3 + X ^ 4 : PowerSeries ℤ) ∧
    (∀ n : ℕ, 2 * (a n : ℤ) = (n : ℤ) ^ 2 + 2 * n - (-1) ^ n * (n + 1) + 3) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a266438
