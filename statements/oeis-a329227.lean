import Mathlib

/-!
# OEIS A329227: Barker's generating function for products of consecutive Padovan numbers

Source: https://oeis.org/A329227 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A329227 (David Nacin, Nov 08 2019), offset 0: Products of consecutive terms of the Padovan
sequence A000931. Formulas: a(n) = A000931(n)*A000931(n+1). G.f.: x^5 / ((1 - 2*x + x^2 -
x^3)*(1 + x - x^3)) (conjectured). - Colin Barker, Nov 08 2019
A000931 is the Padovan sequence: a(n) = a(n-2) + a(n-3) with a(0) = 1, a(1) = a(2) = 0.

Formalization notes:
* `P` is A000931 and a(n) = P(n)*P(n+1), n >= 0.
* Since the denominator of the generating function has constant term 1, the identity
  A(x) = x^5/D for A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = x^5 in the formal power
  series ring over the integers.
* Controls from the entry: the definition gives 0, 0, 0, 0, 0, 1, 1, 2, 4, 6, 12, 20, 35, 63 for
  n = 0..13.
-/

namespace OMA.S_oeis_a329227

open PowerSeries

/-- The Padovan sequence A000931. -/
def P : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | n + 3 => P (n + 1) + P n

/-- A329227(n) = P(n)*P(n+1) (offset 0). -/
def a (n : ℕ) : ℤ := P n * P (n + 1)

/-- Barker's generating function. -/
theorem main :
    PowerSeries.mk a * ((1 - 2 * X + X ^ 2 - X ^ 3) * (1 + X - X ^ 3)) = (X ^ 5 : ℤ⟦X⟧) := by
  sorry

end OMA.S_oeis_a329227
