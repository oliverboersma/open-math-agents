import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# The congruence conjecture for OEIS A000033

Source: https://oeis.org/A000033. In the published coefficient formula for `a(n)`,
put `r = n - k`. The factor `2*n/(n+r) * choose (n+r) (2*r)` becomes
`choose (n+r) (2*r) + choose (n+r-1) (2*r)`. The sequence starts at `n = 1`.

Van Hoeij also stated the corresponding congruence for A000426 on 13 June 2019.
Since `a(n) = n * A000426(n)`, that statement implies this one modulo each prime `p`.
See https://oeis.org/A000426/internal.
-/

open Finset

namespace OMA.S_oeis_a000033

/-- The reindexed coefficient in the OEIS formula. -/
def rookCount (n r : ℕ) : ℕ :=
  (n + r).choose (2 * r) + (n + r - 1).choose (2 * r)

def signedTerm (n r : ℕ) : ℤ :=
  (-1 : ℤ) ^ r * r.factorial * (n - r).choose 2 * rookCount n r

def signedValue (n : ℕ) : ℤ :=
  ∑ r ∈ range (n + 1), signedTerm n r

/-- The terms of A000033 for positive indices. -/
def a (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * signedValue n

/-- Van Hoeij's congruence conjecture for A000033. -/
theorem main : ∀ (n p : ℕ), 0 < n → p.Prime →
    (p : ℤ) ∣ a n + 2 * a (n + p) + a (n + 2 * p) := by
  sorry

end OMA.S_oeis_a000033
