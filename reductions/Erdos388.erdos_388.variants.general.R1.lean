import FormalConjectures.ErdosProblems.«388»
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.NumberTheory.Bertrand

/-!
The right starts below the left multiplier lie in a finite box. Every
later right block has all its prime factors at most its starting point,
and Bertrand's postulate then bounds its length by that starting point.
-/

namespace OMA.R_Erdos388_erdos_388_variants_general_R1

open Finset

def H1 : Prop :=
  ∀ a b m₁ k₁ m₂ k₂ : ℕ, 0 < a → 0 < b → 2 < k₁ → 2 < k₂ → m₁ + k₁ ≤ m₂ →
    a * (∏ i ∈ Icc 1 k₁, (m₁ + i)) = b * (∏ j ∈ Icc 1 k₂, (m₂ + j)) →
    (m₂ < a → k₂ ≤ a * a ^ a) ∧
    (a ≤ m₂ → k₂ < m₂ ∧
      ∀ p ∈ (∏ j ∈ Icc 1 k₂, (m₂ + j)).primeFactors, p ≤ m₂)

def H2 : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b →
    {(m₁, k₁, m₂, k₂) : ℕ × ℕ × ℕ × ℕ |
      2 < k₁ ∧ 2 < k₂ ∧ m₁ + k₁ ≤ m₂ ∧ a ≤ m₂ ∧ k₂ < m₂ ∧
      (∀ p ∈ (∏ j ∈ Icc 1 k₂, (m₂ + j)).primeFactors, p ≤ m₂) ∧
      a * (∏ i ∈ Icc 1 k₁, (m₁ + i)) = b * (∏ j ∈ Icc 1 k₂, (m₂ + j))}.Finite

section Proof

theorem main : H1 → H2 → type_of% @Erdos388.erdos_388.variants.general := by
  intro bounds farFinite a b ha hb
  let box : Set (ℕ × ℕ × ℕ × ℕ) :=
    Set.Iic a ×ˢ (Set.Iic a ×ˢ (Set.Iic a ×ˢ Set.Iic (a * a ^ a)))
  have hBox : box.Finite :=
    (Set.finite_Iic a).prod ((Set.finite_Iic a).prod
      ((Set.finite_Iic a).prod (Set.finite_Iic (a * a ^ a))))
  apply (hBox.union (farFinite a b ha hb)).subset
  rintro ⟨m₁, k₁, m₂, k₂⟩ ⟨hk₁, hk₂, hOrder, hEq⟩
  obtain ⟨hSmall, hFar⟩ := bounds a b m₁ k₁ m₂ k₂ ha hb hk₁ hk₂ hOrder hEq
  by_cases h : m₂ < a
  · apply Or.inl
    change m₁ ≤ a ∧ k₁ ≤ a ∧ m₂ ≤ a ∧ k₂ ≤ a * a ^ a
    exact ⟨by omega, by omega, h.le, hSmall h⟩
  · obtain ⟨hk, hfac⟩ := hFar (by omega)
    exact Or.inr ⟨hk₁, hk₂, hOrder, by omega, hk, hfac, hEq⟩

end Proof

end OMA.R_Erdos388_erdos_388_variants_general_R1
