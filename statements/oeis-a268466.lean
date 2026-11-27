import Mathlib

/-!
# A268466: Smallest m > 1 such that m^m == 1 (mod n)

Source: https://oeis.org/A268466
Credit: @AkiRA-COM-FP

Formalizes the OEIS A268466 conjecture: `a(n) = n + (-1)^n` for infinitely many `n`,
where `a(n)` is the smallest integer `m > 1` with `m^m ≡ 1 [MOD n]`.
-/

namespace OMA.S_oeis_a268466

/-- Smallest integer `m > 1` such that `m^m ≡ 1 [MOD n]`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 < m ∧ m ^ m ≡ 1 [MOD n]}

/-- There are infinitely many `n >= 2` such that `a(n) = n + (-1)^n`. -/
theorem main :
    Set.Infinite {n : ℕ | 2 ≤ n ∧ (a n : ℤ) = (n : ℤ) + (-1 : ℤ) ^ n} := by
  sorry

end OMA.S_oeis_a268466
