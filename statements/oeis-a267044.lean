import Mathlib

/-!
# OEIS A267044: Barker's conjectures for the middle column of Rule 91

Source: https://oeis.org/A267044 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267044 (Robert Price, Jan 09 2016), offset 0: Binary representation of the middle column
of the Rule 91 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 10 2016:
a(n) = (-550+450*(-1)^n+9901*10^n)/9900 for n>1.
a(n) = 10*a(n-1)+a(n-2)-10*a(n-3) for n>4. [Typo corrected by Karl V. Keller, Jr., Mar 16 2022]
G.f.: (1-x^2+x^4) / ((1-x)*(1+x)*(1-10*x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 91 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) writes the middle cells of stages 0..n as binary digits, stage 0
  first, and reads them in base 10, as the entry's program does (FromDigits of the middle column,
  default base 10).
* The recurrence is the corrected one printed in the entry. The statement is the conjunction of
  the three conjectures; the closed form is stated in the rationals and the recurrence in the
  integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power series
  ring over the rationals, and the identity is A = N * D⁻¹, where D has constant term 1.
* Controls from the entry: the definition gives 1, 10, 100, 1000, 10001, 100010, 1000101 for
  n = 0..6.
-/

namespace OMA.S_oeis_a267044

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The middle cell of stage n of Rule 91. -/
def c (n : ℕ) : ℕ := (state 91 n 0).toNat

/-- A267044(n): the middle cells of stages 0..n as binary digits, stage 0 first, read in base 10. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), c k * 10 ^ (n - k)

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 1 < n → (a n : ℚ) = (-550 + 450 * (-1) ^ n + 9901 * 10 ^ n) / 9900) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)) ∧
    A = (1 - X ^ 2 + X ^ 4) * ((1 - X) * (1 + X) * (1 - 10 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a267044
