import Mathlib

/-!
# Are there any Wall–Sun–Sun primes?

Source: https://en.wikipedia.org/wiki/Wall–Sun–Sun_prime
Credit: @sauronsoul-bit

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_are_there_any_wall_sun_sun_primes

-- definitions the statement needs (no sorry, no axiom)

def isPisanoPeriod (p k : ℕ) : Prop := 0 < k ∧ Nat.fib k % p = 0 ∧ Nat.fib (k + 1) % p = 1 ∧ ∀ m, 0 < m → m < k → ¬ (Nat.fib m % p = 0 ∧ Nat.fib (m + 1) % p = 1)

def IsWallSunSunPrime (p : ℕ) : Prop := p.Prime ∧ ∃ k : ℕ, isPisanoPeriod p k ∧ p ^ 2 ∣ Nat.fib k

theorem main : ∃ p : ℕ, IsWallSunSunPrime p := by
  sorry

end OMA.S_wp_are_there_any_wall_sun_sun_primes
