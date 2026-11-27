import Mathlib

/-!
# A269454: Safe primes that are not congruent to -1 mod 8

Source: https://oeis.org/A269454
Credit: @xor2k

Formalizes the OEIS A269454 conjecture: If p and q are two distinct safe primes not congruent
to -1 mod 8 then the order of 2 mod p*q is phi(p*q)/2.

Conventions: a safe prime (A005385) is a prime `p` such that `(p-1)/2` is also prime; in `ℕ`
this is `p.Prime ∧ ((p - 1) / 2).Prime` (for a prime `p` the floor division is exact unless
`p = 2`, and `(2 - 1) / 2 = 0` is not prime, so `2` is correctly excluded). Not congruent to
`-1` mod 8 is `¬ (p : ℤ) ≡ -1 [ZMOD 8]`. The order of 2 mod `p*q` (the least `k > 0` with
`2^k ≡ 1 (mod p*q)`) is `orderOf (2 : ZMod (p * q))`, and `phi` is `Nat.totient`; the
division by 2 is natural-number division (`phi(p*q)` is even here, so it is exact).
-/

namespace OMA.S_oeis_a269454

/-- Safe primes (A005385): primes `p` such that `(p - 1) / 2` is also prime. -/
def IsSafePrime (p : ℕ) : Prop :=
  p.Prime ∧ ((p - 1) / 2).Prime

/-- Membership in A269454: safe primes not congruent to `-1` mod `8`. -/
def InA269454 (p : ℕ) : Prop :=
  IsSafePrime p ∧ ¬ (p : ℤ) ≡ -1 [ZMOD 8]

/-- For distinct `p`, `q` in A269454, the multiplicative order of `2` modulo `p*q`
is `phi(p*q)/2`. -/
theorem main :
    ∀ p q : ℕ, p ≠ q → InA269454 p → InA269454 q →
      orderOf (2 : ZMod (p * q)) = Nat.totient (p * q) / 2 := by
  sorry

end OMA.S_oeis_a269454
