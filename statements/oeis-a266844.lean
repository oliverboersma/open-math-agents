import Mathlib

/-!
# OEIS A266844: Barker's conjectures for the rows of Rule 70

Source: https://oeis.org/A266844 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266844 (Robert Price, Jan 04 2016), offset 0: Binary representation of the n-th iteration
of the Rule 70 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 05 2016 and Apr 18 2019:
a(n) = (2^(n-1)*(-9*(-50)^n-2*5^n+209*50^n))/99.
a(n) = 10*a(n-1)+10000*a(n-2)-100000*a(n-3) for n>2.
G.f.: (1+100*x-1000*x^2) / ((1-10*x)*(1-100*x)*(1+100*x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell (Rule 70 maps 000 to OFF), as CellularAutomaton[rule, {{1},0}, ...] does
  in the entry's program.
* Counting convention: a(n) writes the cells -n..n of stage n as binary digits, leftmost cell
  first, and reads them in base 10, as the entry's program does (Take the middle 2n+1 cells,
  FromDigits with the default base 10).
* The statement is the conjunction of the three conjectures. The closed form, which has no stated
  range, is stated for every n >= 0 after multiplying both sides by 198 = 2*99, using
  2*2^(n-1)*(-50)^n = (-100)^n, 2*2^(n-1)*5^n = 10^n and 2*2^(n-1)*50^n = 100^n:
  198a(n) = 209*100^n - 9*(-100)^n - 2*10^n in the integers. The recurrence is stated in the
  integers. Since the denominator of the generating function has constant term 1, the identity
  A(x) = N/D for A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the formal power series
  ring over the integers.
* Controls from the entry: the definition gives 1, 110, 10100, 1101000, 101010000, 11010100000
  for n = 0..5.
-/

namespace OMA.S_oeis_a266844

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 70 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 70 (state t (i - 1)) (state t i) (state t (i + 1))

/-- A266844(n): the cells -n..n of stage n read as decimal digits, leftmost first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - (n : ℤ)) then 10 ^ (2 * n - k) else 0

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 198 * (a n : ℤ) = 209 * 100 ^ n - 9 * (-100) ^ n - 2 * 10 ^ n) ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 10 * a (n - 1) + 10000 * a (n - 2) - 100000 * a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X)) =
      (1 + 100 * X - 1000 * X ^ 2 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a266844
