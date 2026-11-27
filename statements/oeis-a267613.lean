import Mathlib

/-!
# OEIS A267613: Barker's recurrence and generating function for the rows of Rule 185

Source: https://oeis.org/A267613 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267613 (Robert Price, Jan 18 2016), offset 0: Binary representation of the n-th iteration
of the Rule 185 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 18 2016 and Apr 20 2019:
a(n) = 101*a(n-1) - 100*a(n-2) for n>3.
G.f.: (1-100*x+1010*x^2-900*x^3) / ((1-x)*(1-100*x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 185 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) writes the cells -n..n of stage n as binary digits, leftmost cell
  first, and reads them in base 10, as the entry's program does (Take the middle 2n+1 cells,
  FromDigits with the default base 10).
* The statement is the conjunction of the two conjectures. The recurrence is stated in the
  integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power series
  ring over the rationals, and the identity is A = N * D⁻¹, where D has constant term 1.
* Controls from the entry: the definition gives a(0) = 1 and a(1) = 1.
-/

namespace OMA.S_oeis_a267613

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- Row n (cells -n..n) written in binary digits, leftmost cell first, read in base 10. -/
def rowDigits (s : ℤ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * n + 1), (s ((n : ℤ) - i)).toNat * 10 ^ i

/-- A267613(n). -/
def a (n : ℕ) : ℕ := rowDigits (state 185 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2)) ∧
    A = (1 - 100 * X + 1010 * X ^ 2 - 900 * X ^ 3) * ((1 - X) * (1 - 100 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a267613
