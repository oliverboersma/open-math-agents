import Mathlib

/-!
# OEIS A266251: Barker's conjectures for the OFF cells of Rule 9

Source: https://oeis.org/A266251 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266251 (Robert Price, Dec 25 2015), offset 0: Number of OFF (white) cells in the n-th
iteration of the Rule 9 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Dec 28 2015 and Apr 14 2019:
a(n) = (2*(-1)^n*n+2*n-9*(-1)^n+3)/2 for n>3.
a(n) = 2*a(n-2)-a(n-4) for n>7.
G.f.: x*(3+3*x-x^2-x^3-x^4+2*x^5-x^6) / ((1-x)^2*(1+x)^2).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + x of the rule number, where l, c, x are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 9 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) is the number of OFF cells among the cells -n..n of stage n, as the
  entry's program counts the cells of the truncated row minus its ON cells.
* The statement is the conjunction of the three conjectures. The closed form and the recurrence
  are stated in the integers; in the closed form the numerator is 4n - 6 for even n and 12 for odd
  n, so the integer division by 2 is exact. Since the denominator of the generating function has
  constant term 1, the identity A(x) = N/D for A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N
  in the formal power series ring over the integers.
* Controls from the entry: the definition gives 0, 3, 3, 5 for n = 0..3.
-/

namespace OMA.S_oeis_a266251

open PowerSeries

/-- Wolfram's elementary rule r applied to a neighborhood (left, center, right). -/
def rule (r : ℕ) (l c x : Bool) : Bool := r.testBit (4 * l.toNat + 2 * c.toNat + x.toNat)

/-- Row n of rule r from a single ON cell at 0, the rule applied to every cell. -/
def row (r : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | n + 1 => fun i => rule r (row r n (i - 1)) (row r n i) (row r n (i + 1))

/-- A266251(n): the number of OFF cells among the cells -n..n of row n of Rule 9. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).filter (fun k : ℕ => row 9 n ((k : ℤ) - n) = false)).card

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = (2 * (-1) ^ n * n + 2 * n - 9 * (-1) ^ n + 3) / 2) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 2 * a (n - 2) - a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) =
      X * (3 + 3 * X - X ^ 2 - X ^ 3 - X ^ 4 + 2 * X ^ 5 - X ^ 6) := by
  sorry

end OMA.S_oeis_a266251
