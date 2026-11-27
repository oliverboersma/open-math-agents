import Mathlib

/-!
# A003500: a(n) = 4*a(n-1) - a(n-2) with a(0) = 2, a(1) = 4.

Source: https://oeis.org/A003500
Credit: @LAPRAI

Formalizes the OEIS comment: Tsumura shows that, for prime p, a(p) is composite (contrary to a
conjecture of Juricevic).

Conventions: offset 0; `a` is integer valued. `a(p)` composite means `1 < a(p)` and `a(p)` is not
prime.
-/

namespace OMA.S_oeis_a003500

/-- `a(0) = 2`, `a(1) = 4`, `a(n) = 4*a(n-1) - a(n-2)`. -/
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | n + 2 => 4 * a (n + 1) - a n

/-- For every prime `p`, `a(p)` is composite. -/
theorem main : ∀ p : ℕ, p.Prime → 1 < a p ∧ ¬ Prime (a p) := by
  sorry

end OMA.S_oeis_a003500
