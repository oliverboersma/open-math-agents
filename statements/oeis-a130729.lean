import Mathlib

/-!
# A130729: Fermat numbers of order 3, F(n, 3) = 2^(2^n) + 3

Source: https://oeis.org/A130729
Credit: @AkiRA-COM-FP

Formalizes the OEIS A130729 conjecture (offset 0): if `n` is odd, then `7` divides `2^(2^n) + 3`.
-/

namespace OMA.S_oeis_a130729

/-- Fermat numbers of order 3: `F(n, 3) = 2^(2^n) + 3`. -/
def a (n : ℕ) : ℕ :=
  2 ^ (2 ^ n) + 3

/-- For every odd `n`, `7` divides `2^(2^n) + 3`. -/
theorem main :
    ∀ n : ℕ, Odd n → 7 ∣ a n := by
  sorry

end OMA.S_oeis_a130729
