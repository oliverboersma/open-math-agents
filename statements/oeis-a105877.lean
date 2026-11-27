import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The tens digit of the primes in OEIS A105877

Davide Rotondo conjectured that the tens digit is odd when −5 is a primitive
root and suggested the same for −5 times any square. Max Alekseyev recorded
the four possible residues modulo 20. The sequence starts with 2, which has
no tens digit. Taking t = 1 recovers the original sequence after that exception.

Source: https://oeis.org/A105877
Credit: @erood (Lean formalization with Codex)
-/

namespace OMA.S_oeis_a105877

theorem main : ∀ (p : ℕ), p.Prime → 2 < p → ∀ t : ZMod p,
    IsPrimitiveRoot ((-5 : ZMod p) * t ^ 2) (p - 1) →
      (p % 20 = 11 ∨ p % 20 = 13 ∨ p % 20 = 17 ∨ p % 20 = 19) ∧
      Odd ((p / 10) % 10) := by
  sorry

end OMA.S_oeis_a105877
