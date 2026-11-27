import Mathlib

/-!
# A283050: Integers divisible by the square of their least prime factor

Source: https://oeis.org/A283050
Credit: @AkiRA-COM-FP

Formalizes R. J. Cano's OEIS A283050 conjecture: consecutive terms of the increasing
sequence of integers `m >= 2` divisible by `(minFac m)^2` satisfy `1 <= a(n+1) - a(n) <= 4`.
-/

namespace OMA.S_oeis_a283050

/-- Membership in A283050: integers `m >= 2` divisible by the square of their least prime factor. -/
def IsTerm (m : ℕ) : Prop :=
  2 ≤ m ∧ (Nat.minFac m) ^ 2 ∣ m

/-- The increasing enumeration of A283050 (0-indexed: `a(0) = 4, a(1) = 8, a(2) = 9, ...`). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth IsTerm n

/-- Consecutive gaps in A283050 always lie between `1` and `4` inclusive. -/
theorem main :
    ∀ n : ℕ, 1 ≤ a (n + 1) - a n ∧ a (n + 1) - a n ≤ 4 := by
  sorry

end OMA.S_oeis_a283050
