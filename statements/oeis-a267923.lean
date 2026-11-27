import Mathlib

/-!
# OEIS A267923: Barker's recurrence and generating function for the rows of Rule 245

Source: https://oeis.org/A267923 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267923 (Robert Price, Jan 22 2016), offset 0: Binary representation of the n-th iteration
of the Rule 245 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 23 2016 and Apr 20 2019:
a(n) = 101*a(n-1)-100*a(n-2) for n>2.
G.f.: (1-90*x+10000*x^2) / ((1-x)*(1-100*x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + x of the rule number, where l, c, x are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 245 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) writes the cells -n..n of stage n as binary digits, leftmost cell
  first, and reads them in base 10, as the entry's program does (Take the middle 2n+1 cells,
  FromDigits with the default base 10).
* The statement is the conjunction of the two conjectures; the recurrence is stated in the
  integers. Since the denominator of the generating function has constant term 1, the identity
  A(x) = N/D for A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the formal power series
  ring over the integers.
* Controls from the entry: the definition gives 1, 11, 11011 for n = 0, 1, 2.
-/

namespace OMA.S_oeis_a267923

open PowerSeries

/-- Wolfram's elementary rule r applied to a neighborhood (left, center, right). -/
def rule (r : ℕ) (l c x : Bool) : Bool := r.testBit (4 * l.toNat + 2 * c.toNat + x.toNat)

/-- Row n of rule r from a single ON cell at 0, the rule applied to every cell. -/
def row (r : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | n + 1 => fun i => rule r (row r n (i - 1)) (row r n i) (row r n (i + 1))

/-- A267923(n): the cells -n..n of row n of Rule 245 as decimal digits, leftmost first. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), if row 245 n ((n : ℤ) - k) then 10 ^ k else 0

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 100 * X)) =
      1 - 90 * X + 10000 * X ^ 2 := by
  sorry

end OMA.S_oeis_a267923
