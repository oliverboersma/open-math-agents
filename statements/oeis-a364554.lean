import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Prime.Defs

/-!
# Primes which are triangular numbers divided by n

Source: https://oeis.org/A364554 (Lamine Ngom, OEIS Foundation, CC BY-SA 4.0).
A364555 records the n for which the set of such primes is empty.

For positive n, write n = d*r with d a divisor of n. The proposed prime values
are the integral prime quotients (2*r ± 1)/d and (r ± 1)/(2*d).
Multiplying by the positive denominators expresses the four exact quotients.
-/

namespace OMA.S_oeis_a364554

def triangularPrimes (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∃ k : ℕ, k*(k+1)/2 = n*p}

def divisorPrimes (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∃ d r : ℕ, n = d*r ∧
    (d*p = 2*r+1 ∨ d*p+1 = 2*r ∨ 2*(d*p) = r+1 ∨ 2*(d*p)+1 = r)}

theorem main : ∀ n : ℕ, 0 < n →
    triangularPrimes n = divisorPrimes n ∧ (triangularPrimes n).Finite ∧
      (triangularPrimes n).ncard = (divisorPrimes n).ncard := by
  sorry

end OMA.S_oeis_a364554
