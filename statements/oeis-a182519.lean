import Mathlib

/-!
# A182519: a(n) = prime(n)^(n+1) - prime(n+1)^n.

Source: https://oeis.org/A182519
Credit: @LAPRAI

Formalizes the OEIS comment: Firoozbakht conjecture: a(n) > 0 for all n.

Conventions: offset 1 and `prime(1) = 2`, so `prime(n)` is `Nat.nth Nat.Prime (n - 1)`; `a(n) > 0` is the strict inequality `prime(n+1)^n < prime(n)^(n+1)`.
-/

namespace OMA.S_oeis_a182519

/-- The `n`-th prime, with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Firoozbakht: for every `n ≥ 1`, `prime(n+1)^n < prime(n)^(n+1)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → prime (n + 1) ^ n < prime n ^ (n + 1) := by
  sorry

end OMA.S_oeis_a182519
