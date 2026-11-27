import FormalConjectures.Arxiv.«1601.03081».UniqueCrystalComponents

/-! Separate crystal products whose successor has at most one distinct odd prime divisor.
The first class can be handled by the cofactor of the sum in the successor. -/

open Arxiv.«1601.03081»

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R2

def H1 : Prop :=
  ∀ n a b c d : ℕ, IsCrystalWithComponents n a b → IsCrystalWithComponents n c d →
    (∃ p A B : ℕ, p.Prime ∧ Odd p ∧ n+1 = 2^A*p^B) →
    ({a, b} : Finset ℕ) = {c, d}

def H2 : Prop :=
  ∀ n a b c d : ℕ, IsCrystalWithComponents n a b → IsCrystalWithComponents n c d →
    (∀ p A B : ℕ, p.Prime → Odd p → n+1 ≠ 2^A*p^B) →
    ({a, b} : Finset ℕ) = {c, d}

theorem main : H1 → H2 → type_of% @Arxiv.«1601.03081».crystals_components_unique := by
  classical
  intro hOneOddPrime hMultipleOddPrimes n a b c d hab hcd
  by_cases h : ∃ p A B : ℕ, p.Prime ∧ Odd p ∧ n+1 = 2^A*p^B
  · exact hOneOddPrime n a b c d hab hcd h
  · exact hMultipleOddPrimes n a b c d hab hcd
      (fun p A B hp ho he => h ⟨p,A,B,hp,ho,he⟩)

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R2
