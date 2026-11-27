import Mathlib

/-!
# OEIS A256480: a prime of the form d...dn exists for every n that is odd and not a multiple of 5

Source: https://oeis.org/A256480 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-fable-5-2), submitted by @jleguina.

Entry (Chai Wah Wu, Mar 31 2015), offset 0: Smallest prime obtained by appending n to a nonzero
number with identical digits or 0 if no such prime exists. Comments: a(n) = 0 if n is even or a
multiple of 5. Conjecture: all other terms are nonzero. Conjecture verified for n <= 10^7.
Appending means on the right. The conjecture is also Conjecture 3 of arXiv:1503.08883 by the same
author.

Formalization notes:
* The numbers in question are d...dn: k >= 1 copies of a digit d from 1 to 9, followed by the
  decimal digits of n. `Nat.digits` lists digits from the least significant one, so the digit list
  of d...dn is the digit list of n followed by k copies of d.
* a(n) = 0 means that none of these numbers is prime (a prime is never 0).
* `main` says: if n is odd and not a multiple of 5, then a(n) is not 0.
* Control from the entry: a(17) = 317.
-/

namespace OMA.S_oeis_a256480

/-- The number whose decimal digits are k copies of d followed by the digits of n. -/
def prep (n d k : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n ++ List.replicate k d)

/-- a(n) = 0: no prime is obtained by appending n to a nonzero number with identical digits. -/
def ZeroTerm (n : ℕ) : Prop := ∀ d, 1 ≤ d → d ≤ 9 → ∀ k, 1 ≤ k → ¬ (prep n d k).Prime

/-- Wu's conjecture: a(n) is nonzero for every n that is odd and not a multiple of 5. -/
theorem main : ∀ n : ℕ, n % 2 = 1 → n % 5 ≠ 0 → ¬ ZeroTerm n := by
  sorry

end OMA.S_oeis_a256480
