import Mathlib

/-!
# A244626: Composite numbers k == 5 (mod 8) with 2^((k-1)/2) == k-1 (mod k)

Source: https://oeis.org/A244626
Credit: @AkiRA-COM-FP

Formalizes Conjecture 1 of OEIS A244626: if `p` is an odd prime congruent to `3` or `5`
modulo `8`, then `2^((p - 1) / 2) mod p = p - 1`.
-/

namespace OMA.S_oeis_a244626

/-- For any odd prime `p` with `p % 8 = 3` or `p % 8 = 5`, `2^((p - 1) / 2) % p = p - 1`. -/
theorem main :
    ∀ p : ℕ, p.Prime → (p % 8 = 3 ∨ p % 8 = 5) →
      2 ^ ((p - 1) / 2) % p = p - 1 := by
  sorry

end OMA.S_oeis_a244626
