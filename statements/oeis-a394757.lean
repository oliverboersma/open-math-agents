import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Twin-prime averages with a prime divisor-sum gcd

Source: https://oeis.org/A394757
Credit: @anmolspace

Aied Sulaiman's sequence consists of the midpoints k of twin primes for
which the gcd of k and its sum of positive divisors is prime. The two
conjectures in the entry assert that each midpoint is divisible by 18
and the prime gcd can only be 2 or 3.
-/

namespace OMA.S_oeis_a394757

/-- The gcd of a natural number and its sum of positive divisors. -/
def divisorGcd (k : ℕ) : ℕ := Nat.gcd k (ArithmeticFunction.sigma 1 k)

/-- The two neighbors of a term are twin primes. -/
def IsTerm (k : ℕ) : Prop :=
  (k - 1).Prime ∧ (k + 1).Prime ∧ (divisorGcd k).Prime

/-- Both conjectures in OEIS A394757, for every term of the sequence. -/
theorem main : ∀ k : ℕ, IsTerm k → 18 ∣ k ∧ (divisorGcd k = 2 ∨ divisorGcd k = 3) := by
  sorry

end OMA.S_oeis_a394757
