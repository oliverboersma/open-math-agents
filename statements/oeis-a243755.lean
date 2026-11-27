import Mathlib

/-!
# A243755: Primes p such that p is a primitive root modulo the next prime p' and p' is a primitive root modulo p

Source: https://oeis.org/A243755
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A243755): The sequence contains infinitely many primes.

(The comment continues with a stronger statement involving -p and -p'; only the first sentence is
formalized here.)

Conventions:
* p' is the least prime greater than p.
* g is a primitive root modulo the prime q when its class in `ZMod q` has multiplicative order
  q - 1: `IsPrimitiveRoot (g : ZMod q) (q - 1)`.
-/

namespace OMA.S_oeis_a243755

/-- The least prime greater than `n`. -/
def nextPrime (n : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (n + 1))

/-- Sun's conjecture on A243755: there are infinitely many primes `p` such that `p` is a primitive
root modulo the next prime `p'` and `p'` is a primitive root modulo `p`. -/
theorem main : {p : ℕ | p.Prime ∧ IsPrimitiveRoot (p : ZMod (nextPrime p)) (nextPrime p - 1) ∧
    IsPrimitiveRoot (nextPrime p : ZMod p) (p - 1)}.Infinite := by
  sorry

end OMA.S_oeis_a243755
