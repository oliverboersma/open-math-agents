import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Infix

/-!
# The digit-sum conjecture for OEIS A044279

Sequence by Clark Kimberling. Conjecture by Harvey P. Dale.
Source: https://oeis.org/A044279
Credit: @ptlom (with Codex)

Mathlib lists digits from least to most significant, so [1, 3] represents
the substring 31 in the usual base-nine notation. The digit sum is decimal.
-/

namespace OMA.S_oeis_a044279

theorem main :
    ∀ k : ℕ, 0 < k →
      ([1, 3] : List ℕ).IsInfix (Nat.digits 9 k) →
      ¬ ([1, 3] : List ℕ).IsInfix (Nat.digits 9 (k - 1)) →
      (Nat.digits 10 k).sum % 9 = 0 ∨ (Nat.digits 10 k).sum % 9 = 1 := by
  sorry

end OMA.S_oeis_a044279
