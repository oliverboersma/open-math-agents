import Mathlib

/-!
# A087714: Primes p = prime(i) such that p(i)# - p(i+1) and p(i)# + p(i+1) are both primes

Source: https://oeis.org/A087714
Credit: @niclorusso

Conjecture (in the comments of A087714): there are only 4 primes in this sequence (the known
terms are 5, 13, 19, 367).

Conventions:
* p(i) = prime(i) is the i-th prime with prime(1) = 2 (`Nat.nth Nat.Prime (i - 1)`), and p# is the
  primorial, the product of all primes <= p (Mathlib's `primorial`), so p(i)# = A002110(i).
* For i >= 2, p(i)# >= 2 * p(i) > p(i+1) (Bertrand's postulate), so p(i)# - p(i+1) is a positive integer and the
  natural-number subtraction is exact. For i = 1 the integer 2# - 3 = -1 is not prime, and the
  truncated natural-number difference 0 is not prime either, so i = 1 is correctly excluded.
* "there are only 4 primes in this sequence" is stated as: the set of such primes has exactly 4
  elements (`Set.ncard`, which is 0 for an infinite set, so this also says the set is finite).
-/

namespace OMA.S_oeis_a087714

/-- The `i`-th prime, `prime 1 = 2`. -/
noncomputable def prime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- `p = prime i` is a term of A087714. -/
def IsTerm (p : ℕ) : Prop :=
  ∃ i : ℕ, 1 ≤ i ∧ prime i = p ∧
    (primorial p - prime (i + 1)).Prime ∧ (primorial p + prime (i + 1)).Prime

/-- The conjecture on A087714: there are exactly 4 such primes. -/
theorem main : {p : ℕ | IsTerm p}.ncard = 4 := by
  sorry

end OMA.S_oeis_a087714
