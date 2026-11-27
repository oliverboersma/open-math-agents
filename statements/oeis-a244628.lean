import Mathlib

/-!
# A244628: Composite numbers k == 3 (mod 8) with 2^((k-1)/2) == -1 (mod k)

Source: https://oeis.org/A244628
Credit: @AkiRA-COM-FP

Formalizes Conjecture 1 on OEIS A244628: if `p` is a prime congruent to `3` or `5` mod `8`,
then `2^((p - 1) / 2) mod p = p - 1`.
-/

namespace OMA.S_oeis_a244628

/-- For every prime `p` with `p % 8 = 3` or `p % 8 = 5`, `2^((p - 1) / 2) % p = p - 1`. -/
theorem main :
    ∀ p : ℕ, Nat.Prime p → (p % 8 = 3 ∨ p % 8 = 5) →
      2 ^ ((p - 1) / 2) % p = p - 1 := by
  sorry

end OMA.S_oeis_a244628
