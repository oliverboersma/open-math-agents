import Mathlib

/-!
# A378616: Greatest non prime power <= prime(n).

Source: https://oeis.org/A378616
Credit: @marcelopierry

Conjecture (in the comments of A378616): Equal to A006093(n) = prime(n) - 1 except at terms of
A159611.

Conventions:
* prime(n) is the n-th prime, prime(1) = 2 (`Nat.nth Nat.Prime (n - 1)`); offset 1.
* A prime power is p^k with p prime and k >= 1 (Mathlib's `IsPrimePow`), so 1 is not a prime
  power; this matches the data of A378616 (a(1) = a(2) = a(3) = 1, a(4) = 6, a(5) = 10, ...).
  a(n) is the greatest k <= prime(n) that is not a prime power (`Nat.findGreatest`).
* A159611 lists the indices of the Fermat primes 2^(2^m) + 1 in the sequence of primes
  (2, 3, 7, 55, 6543, ...).
* Except at is stated as an equivalence: for n >= 1, a(n) = prime(n) - 1 exactly when n is not
  a term of A159611.
-/

namespace OMA.S_oeis_a378616

/-- prime(n), with prime(1) = 2. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A378616(n): the greatest non prime power <= prime(n). -/
noncomputable def a (n : ℕ) : ℕ := Nat.findGreatest (fun k => ¬ IsPrimePow k) (prime n)

/-- Membership in A159611: prime(n) is a Fermat prime. -/
def InA159611 (n : ℕ) : Prop := 1 ≤ n ∧ ∃ m : ℕ, prime n = 2 ^ (2 ^ m) + 1

/-- The conjecture: a(n) = prime(n) - 1 exactly off A159611. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = prime n - 1 ↔ ¬ InA159611 n) := by
  sorry

end OMA.S_oeis_a378616
