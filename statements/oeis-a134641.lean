import Mathlib

/-!
# A134641: Prime permutational numbers A134640.

Source: https://oeis.org/A134641
Credit: @ShoQo

Conjecture: "This sequence is finite and complete." (Charles R Greathouse IV, Dec 14 2015: "The
conjecture is correct: in base 2k permutational numbers are divisible by 2k-1 and in base 2k+1
permutational numbers are divisible by k. Hence it suffices to check bases up to 3.")

Formalization notes:
* A134640: n is permutational if for some base b ≥ 1 its b-digit base-b representation, leading
  zeros allowed, uses each of the digits 0, ..., b-1 exactly once; that is,
  n = Σ_{i < b} σ(i) b^i for a permutation σ of {0, ..., b-1}.
* "Finite and complete": the primes that are permutational are exactly 2, 5, 7, 11, 19, the
  listed terms.
-/

namespace OMA.S_oeis_a134641

/-- n has a base-b representation with b digits using each digit 0..b-1 once. -/
def IsPermutational (n : ℕ) : Prop :=
  ∃ b : ℕ, 1 ≤ b ∧ ∃ σ : Equiv.Perm (Fin b), n = ∑ i : Fin b, (σ i : ℕ) * b ^ (i : ℕ)

theorem main : ∀ p : ℕ, p.Prime → (IsPermutational p ↔ p ∈ ({2, 5, 7, 11, 19} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a134641
