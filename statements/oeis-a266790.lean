import Mathlib

/-!
# OEIS A266790: Barker's closed form and generating function for the middle column of Rule 61

Source: https://oeis.org/A266790 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266790 (Robert Price, Jan 03 2016), offset 0: Binary representation of the middle column
of the Rule 61 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 04 2016 and Apr 18 2019:
a(n) = (-9*(-1)^n+1098999991099*2^(n-9)*5^(n-10)-11)/198 for n>9.
G.f.: (1+x-x^3-x^8+x^9+x^10-x^12) / ((1-x)*(1+x)*(1-10*x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 61 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) writes the middle cells of stages 0..n as binary digits, stage 0
  first, and reads them in base 10, as the entry's program does (FromDigits of the middle column,
  default base 10).
* The statement is the conjunction of the two conjectures. The closed form is stated for n > 9 as
  198a(n) = -9(-1)^n + 1098999991099*2^(n-9)*5^(n-10) - 11 in the integers. Since the denominator
  of the generating function has constant term 1, the identity A(x) = N/D for A(x) = Sum_{n >= 0}
  a(n) x^n is stated as A * D = N in the formal power series ring over the integers.
* Controls from the entry: the definition gives 1, 11, 111, 1110, 11101, 111010, 1110101,
  11101010, 111010100, 1110101001, 11101010011 for n = 0..10.
-/

namespace OMA.S_oeis_a266790

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 61 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 61 (state t (i - 1)) (state t i) (state t (i + 1))

/-- A266790(n): the middle cells of stages 0..n as decimal digits, stage 0 first. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), if state t 0 then 10 ^ (n - t) else 0

/-- Barker's closed form and generating function. -/
theorem main :
    (∀ n : ℕ, 9 < n →
      198 * (a n : ℤ) = -9 * (-1) ^ n + 1098999991099 * 2 ^ (n - 9) * 5 ^ (n - 10) - 11) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X)) =
      (1 + X - X ^ 3 - X ^ 8 + X ^ 9 + X ^ 10 - X ^ 12 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a266790
