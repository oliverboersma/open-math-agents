import Mathlib

/-!
# A366274: a(n) is the least k such that prime(n+1+k) >= prime(n)+prime(n+1).

Source: https://oeis.org/A366274
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: for n >= 3, a(n) < n.

Conventions: offset 1, `prime(1) = 2`, so `prime(m)` is `Nat.nth Nat.Prime (m - 1)`. `a(n) < n` for the least such `k` means some `k < n` works.
-/

namespace OMA.S_oeis_a366274

/-- The `m`-th prime, with `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- For `n ≥ 3` some `k < n` has `prime(n) + prime(n+1) ≤ prime(n+1+k)`. -/
theorem main : ∀ n : ℕ, 3 ≤ n → ∃ k : ℕ, k < n ∧ prime n + prime (n + 1) ≤ prime (n + 1 + k) := by
  sorry

end OMA.S_oeis_a366274
