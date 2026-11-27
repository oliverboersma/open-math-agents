import Mathlib.Data.Nat.Prime.Basic

/-!
# A Wieferich prime factor from a large greatest common divisor

Source: https://oeis.org/A331021 (OEIS Foundation, CC BY-SA 4.0).
A001220 defines the base-2 Wieferich primes as the primes p with
p² dividing 2^(p−1)−1. The index k below denotes the candidate sequence value.
-/

namespace OMA.S_oeis_a331021

theorem main : ∀ k : ℕ, 0 < k → k < Nat.gcd (k^2) (2^(k-1)-1) →
    ∃ p : ℕ, p.Prime ∧ p ∣ k ∧ p^2 ∣ 2^(p-1)-1 := by
  sorry

end OMA.S_oeis_a331021
