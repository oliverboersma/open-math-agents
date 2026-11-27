import Mathlib

/-!
# A003592: Numbers of the form 2^i*5^j with i, j >= 0.

Source: https://oeis.org/A003592
Credit: @ShoQo

Conjecture (Zhi-Wei Sun, Apr 18 2023): Each positive integer n not among 1, 4 and 12 can be
written as a sum of finitely many numbers of the form 2^a*5^b + 1 (a,b >= 0) with no one
dividing another. This has been verified for n <= 3700.

Formalization notes:
* The summands are a finite set `S`: two equal summands would divide each other, so "no one
  dividing another" forces them to be distinct. The divisibility condition is stated for
  distinct elements of `S`.
* A single summand is allowed (e.g. 2 = 2^0*5^0 + 1). The empty sum is excluded automatically,
  since `n` is positive.
-/

namespace OMA.S_oeis_a003592

/-- `x` has the form `2^a * 5^b + 1` with `a, b ≥ 0`. -/
def IsTwoFiveSmoothPlusOne (x : ℕ) : Prop :=
  ∃ a b : ℕ, x = 2 ^ a * 5 ^ b + 1

theorem main :
    ∀ n : ℕ, 0 < n → n ≠ 1 → n ≠ 4 → n ≠ 12 →
      ∃ S : Finset ℕ, (∀ x ∈ S, IsTwoFiveSmoothPlusOne x) ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ x ∣ y) ∧
        ∑ x ∈ S, x = n := by
  sorry

end OMA.S_oeis_a003592
