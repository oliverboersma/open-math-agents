import Mathlib

/-!
# A114784: Smallest prime of the form: all twos followed by prime(n), or 0 if no such prime exists

Source: https://oeis.org/A114784
Credit: @niclorusso

A114784(n) is the smallest prime of the form: one or more digits 2 followed by the decimal
digits of prime(n) (so a(n) > prime(n)), or 0 if no such prime exists.

Conjecture (in the comments of A114784): No term is zero except a(1) = a(3) = 0.

Conventions:
* prime(n) is the n-th prime with prime(1) = 2 (`Nat.nth Nat.Prime (n - 1)`); offset 1.
* k >= 1 digits 2 followed by the decimal digits of p is the number
  2 * (10^k - 1)/9 * 10^L + p, where L is the number of decimal digits of p
  (`(Nat.digits 10 p).length`); (10^k - 1)/9 = 11...1 (k ones) is an exact division.
* a(n) = 0 means that no k >= 1 gives a prime. "No term is zero except a(1) = a(3) = 0" is stated
  as: for n >= 1, a(n) /= 0 if and only if n /= 1 and n /= 3.
-/

namespace OMA.S_oeis_a114784

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `k` digits `2` followed by the decimal digits of `p`. -/
def prefixed (k p : ℕ) : ℕ := 2 * ((10 ^ k - 1) / 9) * 10 ^ (Nat.digits 10 p).length + p

/-- `a(n) > 0`: some `k >= 1` digits `2` followed by `prime n` give a prime. -/
def HasPrime (n : ℕ) : Prop := ∃ k : ℕ, 1 ≤ k ∧ (prefixed k (prime n)).Prime

/-- The conjecture on A114784. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (HasPrime n ↔ (n ≠ 1 ∧ n ≠ 3)) := by
  sorry

end OMA.S_oeis_a114784
