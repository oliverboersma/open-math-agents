import Mathlib

/-!
# A213245: Barker's recurrence and g.f. for the number of nonzero 7th powers in GF(2^n)

Source: https://oeis.org/A213245
Credit: @ivillar

A213245 (offset 1): a(n) is the number of nonzero elements of the finite field GF(2^n) that are
7th powers; data 1, 3, 1, 15, 31, 9, 127, 255, 73, ...
Conjectures (Colin Barker, Aug 23 2014), verified by Robert Israel (Nov 20 2016):
a(n) = 9*a(n-3) - 8*a(n-6);
G.f.: x*(4*x^4+6*x^3+x^2+3*x+1) / ( (x-1)*(2*x-1)*(x^2+x+1)*(4*x^2+2*x+1) ).

Formalization notes.
* GF(2^n) is Mathlib's `GaloisField 2 n`; a(n) is the number of x ≠ 0 in it such that x = y^7
  for some y in the field.
* The recurrence is stated for n ≥ 7, i.e. wherever all three terms exist (offset 1).
* The g.f. of the offset-1 sequence is Sum_{n >= 1} a(n) x^n, written as `PowerSeries.mk` of the
  function that is 0 at n = 0 and a(n) for n ≥ 1; the identity is stated over ℤ⟦X⟧,
  cross-multiplied by the denominator, whose constant coefficient is 1.
-/

namespace OMA.S_oeis_a213245

open PowerSeries

/-- A213245: the number of nonzero 7th powers in GF(2^n). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : GaloisField 2 n // x ≠ 0 ∧ ∃ y : GaloisField 2 n, y ^ 7 = x}

/-- Barker's conjectures: the recurrence, and the g.f. cross-multiplied by its denominator. -/
theorem main :
    (∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 9 * (a (n - 3) : ℤ) - 8 * (a (n - 6) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) *
        ((X - 1) * (2 * X - 1) * (X ^ 2 + X + 1) * (4 * X ^ 2 + 2 * X + 1) : PowerSeries ℤ) =
      X * (4 * X ^ 4 + 6 * X ^ 3 + X ^ 2 + 3 * X + 1) := by
  sorry

end OMA.S_oeis_a213245
