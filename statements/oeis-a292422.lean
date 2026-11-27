import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient

/-!
# Infinitely many balanced numbers with two distinct odd prime factors

OEIS A292422 (Jud McCranie, OEIS Foundation, CC BY-SA 4.0):
https://oeis.org/A292422

Broughan and Zhou conjecture this infinitude on page 3 of their paper
https://cs.uwaterloo.ca/journals/JIS/VOL17/Broughan/bro32.pdf.
The OEIS entry orders the odd primes as p < q. Its first example is
418 = 2 * 11 * 19, with divisor sum 720 and totient 180.
Formalization: @ZedingZhang.
-/

namespace OMA.S_oeis_a292422

theorem main : Set.Infinite {x : ℕ |
    (∃ k p q : ℕ, 0 < k ∧ 2 < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ x = 2^k * p * q) ∧
    (∑ d ∈ x.divisors, d) = 4 * x.totient} := by
  sorry

end OMA.S_oeis_a292422
