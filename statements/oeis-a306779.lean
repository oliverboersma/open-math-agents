import Mathlib

/-!
# OEIS A306779: full north-east loops on a rectangular torus

The claimed criterion for a non-intersecting loop to attain length `n*k`
is that `k = 1` or the dimensions have a nontrivial common divisor.

Source: https://oeis.org/A306779
Formalization: @senamakel
-/

namespace OMA.S_oeis_a306779

/-- The number of east steps in the first `i` moves. A false move goes north. -/
def eastCount (w : ℕ → Bool) (i : ℕ) : ℕ :=
  ((Finset.range i).filter fun j => w j = true).card

/-- The position after `i` moves, starting at `(0,0)`. -/
def pos (n k : ℕ) (w : ℕ → Bool) (i : ℕ) : ℕ × ℕ :=
  (eastCount w i % n, (i - eastCount w i) % k)

/-- A loop of full length closes and visits distinct vertices before closing. -/
def HasFullLoop (n k : ℕ) : Prop :=
  ∃ w : ℕ → Bool, pos n k w (n * k) = (0, 0) ∧
    Set.InjOn (pos n k w) (Set.Iio (n * k))

theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    (HasFullLoop n k ↔ k = 1 ∨ 1 < Nat.gcd n k) := by
  sorry

end OMA.S_oeis_a306779
