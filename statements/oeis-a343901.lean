import Mathlib

/-!
# A343901: Number of primes p such that (p - 1) | phi(n)

Source: https://oeis.org/A343901
Credit: @AkiRA-COM-FP

Formalizes the OEIS A343901 conjecture (offset 1): for every `n > 2`, there is at least one
prime `p` such that `(p - 1)` divides `phi(n)` (so `a(n) > 0`).
-/

namespace OMA.S_oeis_a343901

/-- The OEIS sequence A343901: number of primes `p` such that `(p - 1) | phi(n)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ | p.Prime ∧ (p - 1) ∣ Nat.totient n}

/-- For every `n > 2`, `a(n) > 0`. -/
theorem main :
    ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a343901
