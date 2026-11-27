import Mathlib

/-!
# A236464: Primes p with prime(p) + 2 and prime(p) + 6 both prime.

Source: https://oeis.org/A236464
Credit: @darealpandaboi

Conjecture (according to the conjecture in A236472): this sequence contains infinitely many
terms, i.e., there are infinitely many prime triples of the form
{prime(p), prime(p) + 2, prime(p) + 6} with p prime.

Translation notes.
* prime(k) is the k-th prime with prime(1) = 2. Mathlib's Nat.nth Nat.Prime is 0-indexed,
  so prime(k) = Nat.nth Nat.Prime (k - 1); for p prime, p - 1 >= 1 is exact.
* prime(p) is itself prime, so the triple condition is prime(p) + 2 and prime(p) + 6 prime.
* This reading reproduces the listed data: 3, 5, 7, 13, 43, 89, 313, 613, 643, 743, 1171,
  1279, ... (checked by computer).
-/

namespace OMA.S_oeis_a236464

/-- prime(k), the k-th prime, 1-indexed: prime(1) = 2. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

theorem main :
    {p : ℕ | p.Prime ∧ (prime p + 2).Prime ∧ (prime p + 6).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a236464
