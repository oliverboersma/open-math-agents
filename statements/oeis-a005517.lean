import Mathlib

/-!
# A005517: Smallest label f(T) given to a rooted tree T with n nodes in Matula-Goebel labeling.

Source: https://oeis.org/A005517
Credit: @rot13maxi

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a005517

/-- A005517, defined by the explicit formula in the OEIS Formula section
(Emeric Deutsch): `a(1)=1`, `a(2)=2`, and for `n >= 3` the value depends on `n mod 3`. -/
def A005517 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else if n = 2 then 2
  else if n % 3 = 0 then 3 * 5 ^ ((n - 3) / 3)
  else if n % 3 = 1 then 5 ^ ((n - 1) / 3)
  else 9 * 5 ^ ((n - 5) / 3)

/-- Simon Plouffe's conjectured g.f. for A005517:
`z*(1+2*z+3*z^2-z^4)/(1-5*z^3)`.
Multiplying by `1-5*z^3` gives the equivalent coefficient identity below. -/
theorem main :
    (PowerSeries.mk fun n => (A005517 (n + 1) : ℚ)) *
      (1 - 5 * (PowerSeries.X : PowerSeries ℚ) ^ 3) =
      (1 + 2 * (PowerSeries.X : PowerSeries ℚ) + 3 * (PowerSeries.X : PowerSeries ℚ) ^ 2 -
        (PowerSeries.X : PowerSeries ℚ) ^ 4) := by
  sorry

end OMA.S_oeis_a005517
