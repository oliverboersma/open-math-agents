import Mathlib

/-!
# A213243: Barker's formulas for the number of nonzero cubes in GF(2^n)

Source: https://oeis.org/A213243
Credit: @ivillar

A213243 (offset 1): a(n) is the number of nonzero elements of the finite field GF(2^n) that are
cubes; data 1, 1, 7, 5, 31, 21, 127, 85, ...
Conjectures (Colin Barker, Aug 23 2014), verified by Robert Israel (Apr 22 2016):
a(n) = (-1)*((-2+(-1)^n)*(-1+2^n))/3; a(n) = 5*a(n-2) - 4*a(n-4);
G.f.: x*(2*x^2+x+1) / ((x-1)*(x+1)*(2*x-1)*(2*x+1)).

Formalization notes.
* GF(2^n) is Mathlib's `GaloisField 2 n`; a(n) is the number of x ≠ 0 in it such that x = y^3
  for some y in the field.
* The closed form is an identity of rational numbers, for n ≥ 1. The recurrence is stated for
  n ≥ 5, i.e. wherever all three terms exist (offset 1).
* The g.f. of the offset-1 sequence is Sum_{n >= 1} a(n) x^n, written as `PowerSeries.mk` of the
  function that is 0 at n = 0 and a(n) for n ≥ 1; the identity is stated over ℤ⟦X⟧,
  cross-multiplied by the denominator (x-1)*(x+1)*(2*x-1)*(2*x+1), whose constant coefficient is 1.
-/

namespace OMA.S_oeis_a213243

open PowerSeries

/-- A213243: the number of nonzero cubes in GF(2^n). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : GaloisField 2 n // x ≠ 0 ∧ ∃ y : GaloisField 2 n, y ^ 3 = x}

/-- Barker's conjectures: closed form, recurrence, and g.f. (cross-multiplied). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-1) * ((-2 + (-1) ^ n) * (-1 + 2 ^ n)) / 3) ∧
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 5 * (a (n - 2) : ℤ) - 4 * (a (n - 4) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) *
        ((X - 1) * (X + 1) * (2 * X - 1) * (2 * X + 1) : PowerSeries ℤ) =
      X * (2 * X ^ 2 + X + 1) := by
  sorry

end OMA.S_oeis_a213243
