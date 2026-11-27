import Mathlib

/-!
# A082994: Counterexamples to the Ogilvy-Anderson reversal-product square conjecture

Source: https://oeis.org/A082994
Credit: @AkiRA-COM-FP

Formalizes the Ogilvy-Anderson conjecture cited on OEIS A082994:
when a positive integer not divisible by 10 and its base-10 reversal are unequal,
their product is never a square except when both are squares.
(False; counterexamples begin with `k = 288`, where `288 * 882 = 504^2`.)
-/

namespace OMA.S_oeis_a082994

/-- Base-10 digit reversal of a natural number. -/
def rev10 (k : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 k).reverse

/-- Conjecture (Ogilvy-Anderson): if `k > 0`, `k % 10 != 0`, `k != rev10 k`,
and `k * rev10 k` is a square, then both `k` and `rev10 k` are squares. -/
theorem main :
    ∀ k : ℕ, 0 < k → k % 10 ≠ 0 → k ≠ rev10 k →
      IsSquare (k * rev10 k) → IsSquare k ∧ IsSquare (rev10 k) := by
  sorry

end OMA.S_oeis_a082994
