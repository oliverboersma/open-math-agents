import Mathlib

/-!
# OEIS A002114: Eventual modular periodicity of Glaisher's H' numbers

Source: https://oeis.org/A002114
Credit: @gblacher2

Peter Bala conjectured that for each positive modulus, the sequence is
eventually periodic with a period dividing the modulus's Euler totient.
-/

namespace OMA.S_oeis_a002114

/-- The finite-sum formula from the OEIS entry, for indices starting at 1. -/
def glaisherHPrime (n : ℕ) : ℤ :=
  (∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + k) *
    (∑ j ∈ Finset.range (2 * k + 1),
      (-1 : ℤ) ^ j * (Nat.choose (2 * k) j : ℤ) * ((k : ℤ) - j) ^ (2 * n))) / 2

theorem main : ∀ m : ℕ, 0 < m →
    ∃ period first : ℕ, 0 < period ∧ period ∣ m.totient ∧ 0 < first ∧
      ∀ n ≥ first, Int.ModEq (m : ℤ) (glaisherHPrime (n + period)) (glaisherHPrime n) := by
  sorry

end OMA.S_oeis_a002114
