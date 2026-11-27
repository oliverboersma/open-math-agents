import FormalConjectures.ErdosProblems.«386»
import Mathlib.Data.Nat.Choose.Basic

/-!
For a product P of consecutive primes, the triangular-number condition
is detected by the integer discriminant 8P+1.
-/

namespace OMA.R_Erdos386_erdos_386_variants_two_R1

open Filter Finset

def H1 : Prop :=
  ∀ P : ℕ, 6 ≤ P → IsSquare (8 * P + 1) →
    ∃ n : ℕ, 4 ≤ n ∧ n.choose 2 = P ∧ P ≤ n ^ 2

def H2 : Prop :=
  ∀ B : ℕ, ∃ p q : ℕ,
    let P := ∏ i ∈ Ico p q, Nat.nth Nat.Prime i
    B ≤ P ∧ 6 ≤ P ∧ IsSquare (8 * P + 1)

section Proof

theorem main : H1 → H2 → type_of% @Erdos386.erdos_386.variants.two := by
  intro inverseSquare unboundedProducts
  apply frequently_atTop.mpr
  intro K
  obtain ⟨p, q, hLarge, hSix, hSquare⟩ := unboundedProducts (K ^ 2)
  obtain ⟨n, hn4, hn, hUpper⟩ := inverseSquare _ hSix hSquare
  have hKn : K ≤ n := by
    apply le_of_not_gt
    intro hnK
    exact (not_lt_of_ge (hLarge.trans hUpper)) (Nat.pow_lt_pow_left hnK (by decide))
  exact ⟨n, hKn, by omega, p, q, hn⟩

end Proof

end OMA.R_Erdos386_erdos_386_variants_two_R1
