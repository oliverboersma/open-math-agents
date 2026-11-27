import Mathlib

/-!
# A257924: Primes p with p-1, p+1, prime(p)-1 and prime(p)+1 all practical.

Source: https://oeis.org/A257924
Credit: @darealpandaboi

Conjecture (Zhi-Wei Sun): The sequence contains infinitely many terms. In other words, there
are infinitely many prime numbers p such that {p-1, p, p+1} and {prime(p)-1, prime(p),
prime(p)+1} are both sandwiches of the first kind (A210479).

Translation notes.
* A practical number (A005153) is a positive integer n such that every smaller nonnegative
  integer is a sum of distinct divisors of n (0 is the empty sum).
* prime(k) is the k-th prime with prime(1) = 2, i.e. Nat.nth Nat.Prime (k - 1).
* For p prime, p - 1 >= 1 and prime(p) - 1 >= 1, so the subtractions are exact.
* This reading reproduces the listed data: 3, 7, 31, 89, 199, 8009, 11551, ... (checked by
  computer).
-/

namespace OMA.S_oeis_a257924

/-- n is practical: every m < n is a sum of distinct divisors of n. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m < n → ∃ s ⊆ n.divisors, ∑ d ∈ s, d = m

/-- prime(k), the k-th prime, 1-indexed: prime(1) = 2. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

theorem main :
    {p : ℕ | p.Prime ∧ IsPractical (p - 1) ∧ IsPractical (p + 1) ∧
      IsPractical (prime p - 1) ∧ IsPractical (prime p + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a257924
