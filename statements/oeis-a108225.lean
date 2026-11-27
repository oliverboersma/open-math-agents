import Mathlib

/-!
# A108225: a(0) = 0, a(1) = 2; for n >= 2, a(n) = (a(n-1) + a(n-2))*(a(n-1) - a(n-2) + 1)/2

Source: https://oeis.org/A108225
Credit: @xor2k

Formalizes the OEIS A108225 conjecture (R. J. Mathar, Apr 23 2007): a(n) = A006894(n) + 1.

Conventions:
* A108225 has offset 0; A006894 has offset 1, so the conjecture is stated for `n ≥ 1`;
* A006894 (number of planted 3-trees of height < n) is given by its OEIS recurrence
  `A006894(1) = 1`, `A006894(n+1) = A006894(n)*(A006894(n)+1)/2 + 1`; here it is `b` with the
  auxiliary seed `b 0 = 0` (as in the OEIS remark a(n) = A000124(a(n-1)) assuming a(0) = 0), which
  yields `b 1 = 1` and is not itself part of the claim;
* `/` is floor division on `ℕ`; all divisions in both recurrences are exact, and the natural
  subtraction `a(n-1) - a(n-2)` never truncates because A108225 is nondecreasing.
-/

namespace OMA.S_oeis_a108225

/-- A108225: `a(0) = 0`, `a(1) = 2`, `a(n) = (a(n-1) + a(n-2))*(a(n-1) - a(n-2) + 1)/2`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | n + 2 => (a (n + 1) + a n) * (a (n + 1) - a n + 1) / 2

/-- A006894 via `b(n+1) = b(n)*(b(n)+1)/2 + 1`, seeded with `b 0 = 0` so that `b 1 = 1`. -/
def b : ℕ → ℕ
  | 0 => 0
  | n + 1 => b n * (b n + 1) / 2 + 1

/-- For every `n ≥ 1`, `A108225(n) = A006894(n) + 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = b n + 1 := by
  sorry

end OMA.S_oeis_a108225
