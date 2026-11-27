import Mathlib

/-!
# OEIS A266594: Barker's conjectures for the ON cells of Rule 37

Source: https://oeis.org/A266594 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266594 (Robert Price, Jan 01 2016), offset 0: Total number of ON (black) cells after n
iterations of the Rule 37 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 02 2016 and Apr 18 2019:
a(n) = (n^2-(-1)^n*(n-3)+5)/2 for n>0.
a(n) = a(n-1)+2*a(n-2)-2*a(n-3)-a(n-4)+a(n-5) for n>5.
G.f.: (1+x+x^2-2*x^4+3*x^5) / ((1-x)^3*(1+x)^2).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 37 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: as in the entry's program, row k counts the ON cells among the cells
  -k..k of stage k, and a(n) is the sum of these counts for k = 0..n.
* The statement is the conjunction of the three conjectures. The closed form is stated in the
  rationals and the recurrence in the integers. The generating function is A(x) = Sum_{n >= 0}
  a(n) x^n in the formal power series ring over the rationals, and the identity is A = N * D⁻¹,
  where D has constant term 1.
* Controls from the entry: the definition gives a(0) = 1 and a(1) = 2.
-/

namespace OMA.S_oeis_a266594

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The number of ON cells of row k among the cells -k..k. -/
noncomputable def rowCount (s : ℤ → Bool) (k : ℕ) : ℕ :=
  ((Finset.Icc (-(k : ℤ)) k).filter fun x => s x = true).card

/-- A266594(n): the total number of ON cells in rows 0..n. -/
noncomputable def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), rowCount (state 37 k) k

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℚ) = ((n : ℚ) ^ 2 - (-1) ^ n * ((n : ℚ) - 3) + 5) / 2) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    A = (1 + X + X ^ 2 - 2 * X ^ 4 + 3 * X ^ 5) * ((1 - X) ^ 3 * (1 + X) ^ 2)⁻¹ := by
  sorry

end OMA.S_oeis_a266594
