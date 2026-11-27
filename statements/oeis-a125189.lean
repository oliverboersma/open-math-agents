/-
OEIS A125189, the recurrence conjectured by R. J. Mathar and the ordinary
generating function's differential equation given by Robert Israel.
Reference: https://oeis.org/A125189
Credit: @Heart-galaxy
Text credit: OEIS Foundation, CC BY-SA 4.0.

The entry gives a radical ordinary generating function. We take the
formal square root with constant coefficient one. Its numerator has zero
constant coefficient, so division by the initial X shifts coefficients.
The displayed recurrence has all its terms defined from index 8 onward.
-/

import Mathlib

namespace OMA.S_oeis_a125189

open PowerSeries

abbrev Series := PowerSeries ℚ

noncomputable def radicand : Series := 1 - 2 * X ^ 2 - 3 * X ^ 4

noncomputable def radical : Series :=
  (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (radicand - 1)

noncomputable def numeratorHead : Series := 1 - X ^ 4

noncomputable def radicalFactor : Series := (1 + X) ^ 2

noncomputable def denominatorFactor : Series := 2 * (X ^ 3 + X ^ 2 + X - 1)

noncomputable def removeX (f : Series) : Series := mk (fun n => coeff (n + 1) f)

/-- The published ordinary generating function, with the initial X removed
from its numerator by shifting its coefficients. -/
noncomputable def gf : Series :=
  removeX (numeratorHead - radicalFactor * radical) * denominatorFactor⁻¹

noncomputable def a (n : ℕ) : ℚ := coeff n gf

noncomputable def odeConstant : Series :=
  C 3 * X ^ 7 + C 1 * X ^ 6 + C 3 * X ^ 5 + C 5 * X ^ 4 +
    C 1 * X ^ 3 + C 3 * X ^ 2 + C 1 * X ^ 1 - C 1 * X ^ 0

noncomputable def odeValue : Series :=
  C 3 * X ^ 7 - C 1 * X ^ 6 + C 15 * X ^ 5 + C 3 * X ^ 4 +
    C 1 * X ^ 3 - C 3 * X ^ 2 - C 3 * X ^ 1 + C 1 * X ^ 0

noncomputable def odeDerivative : Series :=
  C 3 * X ^ 9 + C 6 * X ^ 8 + C 8 * X ^ 7 + C 4 * X ^ 6 -
    C 2 * X ^ 4 - C 4 * X ^ 3 + C 1 * X ^ 1

theorem main :
    odeConstant + odeValue * gf + odeDerivative * derivative ℚ gf = 0 ∧
    (∀ n : ℕ, 8 ≤ n →
      ((n : ℚ) + 1) * a n - 3 * a (n - 1) + (-4 * (n : ℚ) + 5) * a (n - 2) +
      (-2 * (n : ℚ) + 7) * a (n - 3) + 3 * a (n - 4) +
      (4 * (n : ℚ) - 5) * a (n - 5) + (8 * (n : ℚ) - 49) * a (n - 6) +
      3 * (2 * (n : ℚ) - 13) * a (n - 7) + 3 * ((n : ℚ) - 8) * a (n - 8) = 0) := by
  sorry

end OMA.S_oeis_a125189
