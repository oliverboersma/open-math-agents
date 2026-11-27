import Mathlib

/-!
# A263450: Smallest k > 0 such that the decimal representation of prime(n)^k contains a zero

Source: https://oeis.org/A263450
Credit: @AkiRA-COM-FP

Formalizes the OEIS A263450 conjecture (offset 1): there are infinitely many `n >= 1`
such that `a(n) = 1`, where `a(n)` is the smallest `k > 0` for which `prime(n)^k`
contains the digit `0` in base 10.
-/

namespace OMA.S_oeis_a263450

/-- Smallest positive `k` such that `0` appears among the base-10 digits of `prime(n)^k`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ 0 ∈ Nat.digits 10 ((Nat.nth Nat.Prime (n - 1)) ^ k)}

/-- There are infinitely many `n >= 1` such that `a(n) = 1`. -/
theorem main :
    Set.Infinite {n : ℕ | 1 ≤ n ∧ a n = 1} := by
  sorry

end OMA.S_oeis_a263450
