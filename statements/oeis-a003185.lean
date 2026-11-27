import Mathlib

/-!
# First differences of OEIS A003185

R. J. Mathar conjectured that the first differences of A003185, indexed from
zero, agree with A063164 starting at index 2. The latter sequence is indexed
from 1. Its term at index `m` is the complex dimension of the space of cusp
forms of weight `2 * m` for Γ₀(96).

Sources: https://oeis.org/A003185 and https://oeis.org/A063164
Credit: @yuka30240
-/

namespace OMA.S_oeis_a003185

open CongruenceSubgroup

/-- The term of A003185 at index `n`. -/
def a (n : ℕ) : ℤ := (4 * (n : ℤ) + 1) * (4 * (n : ℤ) + 5)

theorem main : ∀ n : ℕ, a (n + 1) - a n =
    (Module.finrank ℂ (CuspForm (Gamma0 96) (2 * ((n : ℤ) + 2))) : ℤ) := by
  sorry

end OMA.S_oeis_a003185
