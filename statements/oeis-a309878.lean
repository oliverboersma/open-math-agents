import Mathlib

/-!
# A309878: The real part of b(n) where b(n) = (n + b(n-1)) * (1 + i) with b(-1)=0; i = sqrt(-1).

Source: https://oeis.org/A309878
Credit: @JeremyDevs

Formalizes two of the conjectures of Colin Barker (Aug 21 2019) recorded in OEIS A309878:
* a(n) = 4*a(n-1) - 7*a(n-2) + 6*a(n-3) - 2*a(n-4) for n > 3;
* a(n) = i*((1-i)^n - (1+i)^n + i*n) where i = sqrt(-1).
The entry notes (Sela Fried, Jul 27 2024) that the conjectures hold true, so this is a known
result; the statement below is its Lean form.

Conventions:
* b(-1) = 0 and b(n) = (n + b(n-1)) * (1 + i) for n ≥ 0, so b(0) = (0 + 0) * (1 + i) = 0. The
  function `b` below is indexed by `n ≥ 0`, starting from this value b(0) = 0, with
  b(n+1) = ((n+1) + b(n)) * (1 + i). Its values are 0, 1+i, 2+4i, 1+9i, -4+14i, ... as in the
  EXAMPLE section of the entry.
* a(n) = Re b(n) (offset 0), a real number (an integer in fact): 0, 1, 2, 1, -4, -13, -22, ...
* The recurrence is asserted for every `n > 3`, where the indices `n - 1, ..., n - 4` are genuine.
* The closed form is asserted for every `n ≥ 0`, as an identity in `ℂ` between the real number
  a(n) and the complex expression.
* Barker's third conjecture, the generating function x*(1 - 2*x) / ((1 - x)^2*(1 - 2*x + 2*x^2)),
  is not stated separately: given the first four terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a309878

/-- b(0) = 0, b(n+1) = ((n+1) + b(n)) * (1 + i). -/
noncomputable def b : ℕ → ℂ
  | 0 => 0
  | n + 1 => (((n : ℂ) + 1) + b n) * (1 + Complex.I)

/-- A309878: a(n) = Re b(n). -/
noncomputable def a (n : ℕ) : ℝ := (b n).re

/-- Barker's conjectures: the linear recurrence for `n > 3` and the closed form. -/
theorem main :
    (∀ n : ℕ, 3 < n → a n = 4 * a (n - 1) - 7 * a (n - 2) + 6 * a (n - 3) - 2 * a (n - 4)) ∧
    (∀ n : ℕ, ((a n : ℝ) : ℂ) =
      Complex.I * ((1 - Complex.I) ^ n - (1 + Complex.I) ^ n + Complex.I * (n : ℂ))) := by
  sorry

end OMA.S_oeis_a309878
