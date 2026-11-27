import Mathlib

/-!
# Infinitely many zeros of a Möbius-weighted gcd sum

Source: Nilotpal Kanti Sinha, https://mathoverflow.net/questions/336569
Credit: @gxd12312
-/

namespace OMA.S_mo_336569

open scoped BigOperators

/-- Are there infinitely many positive integers `n` for which the sum of
`μ(r) * gcd(n, r)` over `1 ≤ r < n` is zero? -/
theorem main :
    Set.Infinite {n : ℕ | 0 < n ∧
      (∑ r ∈ Finset.Ico 1 n, ArithmeticFunction.moebius r * (Nat.gcd n r : ℤ)) = 0} := by
  sorry

end OMA.S_mo_336569
