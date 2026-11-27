import Mathlib

/-!
# A090526: Primes arising in A090525, or 0 if A090525(n) = 0

Source: https://oeis.org/A090526
Credit: @AkiRA-COM-FP

Formalizes the OEIS A090526 conjecture (offset 2): no term of A090526 is zero.
-/

namespace OMA.S_oeis_a090526

/-- A090525: least positive integer `k` such that `floor(n^n / k)` is prime, or `0` if none exists. -/
noncomputable def a090525 (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ (n ^ n / k).Prime}

/-- A090526: the prime `floor(n^n / A090525(n))`, or `0` if `A090525(n) = 0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  if a090525 n = 0 then 0 else n ^ n / a090525 n

/-- No term of A090526 is zero for `n >= 2`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a090526
