import Mathlib

/-!
# A139035: Primes of the form 4*k+3 with primitive root -2.

Source: https://oeis.org/A139035
Credit: @ShoQo

Conjecture (Davide Rotondo, Dec 20 2024): "primes that have both primitive root -2 and -4."
(Jianing Song, May 30 2026: "The conjecture above is correct.")

Formalization notes:
* a is a primitive root modulo a prime p iff a generates (ZMod p)ˣ, i.e. the multiplicative order
  of a in `ZMod p` is p - 1 (`orderOf`, which is 0 for a ≡ 0).
* The claim: for every prime p, (p ≡ 3 (mod 4) and -2 is a primitive root mod p) iff (-2 and -4
  are both primitive roots mod p).
-/

namespace OMA.S_oeis_a139035

theorem main : ∀ p : ℕ, p.Prime →
    ((p % 4 = 3 ∧ orderOf (-2 : ZMod p) = p - 1) ↔
      (orderOf (-2 : ZMod p) = p - 1 ∧ orderOf (-4 : ZMod p) = p - 1)) := by
  sorry

end OMA.S_oeis_a139035
