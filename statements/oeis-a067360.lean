import Mathlib

/-!
# A067360: a(n) = 17^n sin(2n arctan(1/4)) or numerator of tan(2n arctan(1/4)).

Source: https://oeis.org/A067360
Credit: @JeremyDevs

Formalizes two of the conjectures of Colin Barker (Jul 25 2017) recorded in OEIS A067360:
* a(n) = 30*a(n-1) - 289*a(n-2) for n > 2;
* a(n) = i*((15 - 8*i)^n - (15 + 8*i)^n)/2 where i = sqrt(-1).

Conventions:
* The sequence has offset 1 and is defined by the formula of its title and FORMULA section,
  a(n) = 17^n sin(2n arctan(1/4)), a real number (an integer in fact): 8, 240, 4888, 77280, ...
  The function `a` below is this formula for every natural `n`; only `n ≥ 1` is used.
* The recurrence is asserted for every `n > 2`, as in the source; the indices `n - 1`, `n - 2`
  are then at least 1.
* The closed form is asserted for every `n ≥ 1`, as an identity in `ℂ` between the real number
  a(n) and the complex expression.
* Barker's third conjecture, the generating function 8*x / (1 - 30*x + 289*x^2), is not stated
  separately: given the first two terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a067360

/-- A067360: a(n) = 17^n sin(2n arctan(1/4)). -/
noncomputable def a (n : ℕ) : ℝ := 17 ^ n * Real.sin (2 * (n : ℝ) * Real.arctan (1 / 4))

/-- Barker's conjectures: the linear recurrence for `n > 2` and the closed form. -/
theorem main :
    (∀ n : ℕ, 2 < n → a n = 30 * a (n - 1) - 289 * a (n - 2)) ∧
    (∀ n : ℕ, 1 ≤ n → ((a n : ℝ) : ℂ) =
      Complex.I * ((15 - 8 * Complex.I) ^ n - (15 + 8 * Complex.I) ^ n) / 2) := by
  sorry

end OMA.S_oeis_a067360
