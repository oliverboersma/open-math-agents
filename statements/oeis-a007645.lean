import Mathlib.Data.Nat.Prime.Basic

/-! Tisdale's union identity for generalized cuban primes, OEIS A007645. -/

namespace OMA.S_oeis_a007645

def GeneralizedCubanPrime (p : ℕ) : Prop := p.Prime ∧ (p % 3 = 0 ∨ p % 3 = 1)

def IsA002383 (p : ℕ) : Prop := p.Prime ∧ ∃ k : ℕ, p = k ^ 2 + k + 1

def IsA162471 (p : ℕ) : Prop :=
  (p.Prime ∧ ∃ k : ℕ, p ∣ k ^ 2 + k + 1) ∧ ¬ IsA002383 p

theorem main : ∀ p : ℕ, GeneralizedCubanPrime p ↔ IsA002383 p ∨ IsA162471 p := by
  sorry

end OMA.S_oeis_a007645
