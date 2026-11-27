import Mathlib

/-!
# A001076: Denominators of continued fraction convergents to sqrt(5).

Source: https://oeis.org/A001076
Credit: @rot13maxi

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a001076

/-- A001076: denominators of the continued fraction convergents to `sqrt 5`,
defined by the OEIS recurrence `a(n) = 4*a(n-1) + a(n-2)`, `a(0)=0`, `a(1)=1`. -/
def A001076 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 4 * A001076 (n + 1) + A001076 n

/-- A001077: numerators of the continued fraction convergents to `sqrt 5`,
defined by the OEIS recurrence `a(n) = 4*a(n-1) + a(n-2)`, `a(0)=1`, `a(1)=2`. -/
def A001077 : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => 4 * A001077 (n + 1) + A001077 n

/-- Creighton Dement's conjecture on A001076 (OEIS Formula section):
`2*a(n+1) = a(n+2) - A001077(n+1)` for every `n`. -/
theorem main : ∀ n : ℕ,
    (2 : ℤ) * (A001076 (n + 1) : ℤ) =
      (A001076 (n + 2) : ℤ) - (A001077 (n + 1) : ℤ) := by
  sorry

end OMA.S_oeis_a001076

