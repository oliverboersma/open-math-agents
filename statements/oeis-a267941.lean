import Mathlib

/-!
# OEIS A267941: Barker's recurrence and generating function for the rows of Rule 253

Source: https://oeis.org/A267941 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267941 (Robert Price, Jan 22 2016), offset 0: Decimal representation of the n-th iteration
of the Rule 253 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 23 2016 and Apr 16 2019:
a(n) = 5*a(n-1)-4*a(n-2) for n>3.
G.f.: (1-2*x+20*x^2-16*x^3) / ((1-x)*(1-4*x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 253 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) reads the cells -n..n of stage n as a binary number with the leftmost
  cell most significant, as the entry's program does (Take the middle 2n+1 cells, FromDigits base
  2).
* The statement is the conjunction of the two conjectures of the block quoted above; the entry's
  later empirical formula a(n) = 2^(2n+1) - 1 for n>1 (Colin Barker, Nov 26 2016) is not part of
  this problem. The recurrence is stated in the integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in
  the formal power series ring over the rationals, and the identity is A = N * D⁻¹, where D has
  constant term 1.
* Controls from the entry: the definition gives a(0) = 1 and a(1) = 3.
-/

namespace OMA.S_oeis_a267941

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- Row n (cells -n..n) read as a binary number, leftmost cell most significant. -/
def rowValue (s : ℤ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * n + 1), (s ((n : ℤ) - i)).toNat * 2 ^ i

/-- A267941(n). -/
def a (n : ℕ) : ℕ := rowValue (state 253 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 5 * a (n - 1) - 4 * a (n - 2)) ∧
    A = (1 - 2 * X + 20 * X ^ 2 - 16 * X ^ 3) * ((1 - X) * (1 - 4 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a267941
