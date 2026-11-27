import Mathlib

/-!
# A272027: a(n) = 3 * sigma(n)

Source: https://oeis.org/A272027
Credit: @AkiRA-COM-FP

Formalizes Omar E. Pol's OEIS A272027 conjectures (offset 1):
1. `3 * sigma(n) = sigma(2*n)` iff `n` is odd.
2. For any prime `p` and `n >= 1`, `(p + 1) * sigma(n) = sigma(p*n)` iff `¬ (p ∣ n)`.
-/

namespace OMA.S_oeis_a272027

/-- Sequence `a(n) = 3 * sigma(n)`. -/
def a (n : ℕ) : ℕ :=
  3 * ArithmeticFunction.sigma 1 n

/-- Conjectures 1 and 2 on OEIS A272027. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n = ArithmeticFunction.sigma 1 (2 * n) ↔ Odd n)) ∧
    (∀ p : ℕ, p.Prime → ∀ n : ℕ, 1 ≤ n →
      ((p + 1) * ArithmeticFunction.sigma 1 n = ArithmeticFunction.sigma 1 (p * n) ↔
        ¬ (p ∣ n))) := by
  sorry

end OMA.S_oeis_a272027
