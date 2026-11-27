import Mathlib

/-!
# A263244: Binary representation of the n-th iteration of the 'Rule 155' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A263244
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = a(n-1)+10000*a(n-2)-10000*a(n-3) for n>3
* G.f.: (1+100*x-90*x^2+1100*x^3) / ((1-x)*(1-100*x)*(1+100*x))
* a(n) = floor(91*100^((n-1)/2)*10^n/9) for odd n
* a(n) = floor(901*100^(n/2 - 1)*10^n/9) for even n

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a263244

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A263244(n): the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1),
    if cell 155 n ((j : ℤ) - n) then (10 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n > 3, a n = a (n - 1) + 10000 * a (n - 2) - 10000 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 100 * X) * (1 + 100 * X)) = 1 + 100 * X - 90 * X ^ 2 + 1100 * X ^ 3) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = ((⌊(91 * (100 : ℚ) ^ (((n : ℤ) - 1) / 2) * (10 : ℚ) ^ (n : ℤ) / 9 : ℚ)⌋ : ℤ) : ℚ)) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = ((⌊(901 * (100 : ℚ) ^ ((n : ℤ) / 2 - 1) * (10 : ℚ) ^ (n : ℤ) / 9 : ℚ)⌋ : ℤ) : ℚ)) := by
  sorry

end OMA.S_oeis_a263244
