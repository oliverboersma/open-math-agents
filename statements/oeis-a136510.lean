import Mathlib

/-!
# OEIS A136510

Reinhard Zumkeller conjectured that for each positive integer `n` there is a
least exponent `k > 1` such that the binary expansion of `n` occurs as a
contiguous block in the binary expansion of `n ^ k`. Mathlib writes both
digit lists from least to most significant. Reversing both words preserves
contiguous containment.

Source: https://oeis.org/A136510
-/

namespace OMA.S_oeis_a136510

def exponents (n : ℕ) : Set ℕ :=
  {k | 1 < k ∧ (Nat.digits 2 n).IsInfix (Nat.digits 2 (n ^ k))}

theorem main : ∀ n : ℕ, 0 < n → ∃ k : ℕ, IsLeast (exponents n) k := by
  sorry

end OMA.S_oeis_a136510
