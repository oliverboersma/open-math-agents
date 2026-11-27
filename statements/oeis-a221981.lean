import Mathlib

/-!
# OEIS A221981: the primes q = 4p+1 with p = 2 mod 5 have primitive root 40, and 8q+1 root 10

Source: https://oeis.org/A221981 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A221981 (Jonathan Sondow, Feb 02 2013), offset 1: Primes q = 4*p+1, where p == 2 (mod 5)
is also prime. Comments include: If the sequence is infinite, then Artin's conjecture (every
nonsquare integer n != -1 is a primitive root of infinitely many primes q) is true for n = 10. The
sequence is infinite under Dickson's conjecture, thus Dickson's conjecture implies Artin's
conjecture for n = 10. - Charles R Greathouse IV, Apr 18 2013. Two conjectures: (a) These primes
have primitive root 40; (b) if a(n)*8 + 1 is prime then it has primitive root 10. - Davide
Rotondo, Dec 31 2024

Formalization notes:
* The statement is the conjunction of Rotondo's conjectures (a) and (b). The comments on Artin's
  and Dickson's conjectures state implications that rest on those conjectures and are not
  conjectures of the entry themselves, so they are not part of the statement.
* A prime r has primitive root g when g has multiplicative order r - 1 modulo r, written
  `orderOf (g : ZMod r) = r - 1`.
* The terms of the sequence are described by the membership predicate `InSeq`.
* Controls from the entry: 29, 149 and 269 satisfy `InSeq`.
-/

namespace OMA.S_oeis_a221981

/-- q is a term of A221981: q is prime and q = 4p + 1 for a prime p = 2 mod 5. -/
def InSeq (q : ℕ) : Prop := q.Prime ∧ ∃ p, p.Prime ∧ p % 5 = 2 ∧ q = 4 * p + 1

/-- Rotondo's conjectures (a) and (b). -/
theorem main : (∀ q : ℕ, InSeq q → orderOf (40 : ZMod q) = q - 1) ∧
    (∀ q : ℕ, InSeq q → (8 * q + 1).Prime → orderOf (10 : ZMod (8 * q + 1)) = 8 * q + 1 - 1) := by
  sorry

end OMA.S_oeis_a221981
