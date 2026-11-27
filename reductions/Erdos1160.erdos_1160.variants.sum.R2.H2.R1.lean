import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2
import Mathlib.GroupTheory.Nilpotent

/-! Separate group counts at orders below a power of two into nilpotent and
nonnilpotent populations. For nilpotent groups the product of Sylow types
gives an independent estimate whenever the exponent of two in the order is
at most 7m/11. This includes every odd order. -/

open Filter CategoryTheory Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1

/-- Nilpotent groups whose Sylow exponents are small enough for the elementary
presentation count. Every odd prime power below the cutoff has exponent at
most 7m/11, since 2^11 ≤ 3^7. -/
def H1 : Prop := ∀ᶠ m : ℕ in atTop, ∀ n ∈ Finset.Ico 1 (2^m),
  11*n.factorization 2 ≤ 7*m →
  2^(2*m) * (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsNilpotent G}).ncard ≤ g (2^(m-2))

/-- Nilpotent groups with a large Sylow two-subgroup and nontrivial odd part. -/
def H2 : Prop := ∀ᶠ m : ℕ in atTop, ∀ n ∈ Finset.Ico 1 (2^m),
  (¬ ∃ k : ℕ, n = 2^k) → 7*m < 11*n.factorization 2 →
  (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsNilpotent G}).ncard ≤
    2^(m-2)*g (2^(m-2))

/-- The remaining group structures, which do not decompose as the product of
their Sylow subgroups. -/
def H3 : Prop := ∀ᶠ m : ℕ in atTop, ∀ n ∈ Finset.Ico 1 (2^m),
  (¬ ∃ k : ℕ, n = 2^k) →
  (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ ¬Group.IsNilpotent G}).ncard ≤
    2^(m-2)*g (2^(m-2))

theorem main : H1 → H2 → H3 → OMA.R_Erdos1160_erdos_1160_variants_sum_R2.H2 := by
  intro small large other
  filter_upwards [small, large, other, eventually_ge_atTop 2] with m hs hl ho hm
  intro n hn hnp
  classical
  let A := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsNilpotent G}
  let B := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ ¬Group.IsNilpotent G}
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n} = A ∪ B := by
    ext x
    constructor
    · rintro ⟨G, hG, rfl⟩
      by_cases h : Group.IsNilpotent G
      · exact Or.inl ⟨G, ⟨hG, h⟩, rfl⟩
      · exact Or.inr ⟨G, ⟨hG, h⟩, rfl⟩
    · rintro (⟨G, ⟨hG, _⟩, rfl⟩ | ⟨G, ⟨hG, _⟩, rfl⟩) <;> exact ⟨G, hG, rfl⟩
  have boundA : A.ncard ≤ 2^(m-2)*g (2^(m-2)) := by
    by_cases h : 11*n.factorization 2 ≤ 7*m
    · exact (Nat.le_mul_of_pos_left A.ncard (by positivity : 0 < 2^(2*m))).trans
        ((hs n hn h).trans (Nat.le_mul_of_pos_left _ (by positivity)))
    · exact hl n hn hnp (by omega)
  have boundB : B.ncard ≤ 2^(m-2)*g (2^(m-2)) := ho n hn hnp
  change (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n}).ncard ≤ _
  rw [cover]
  calc
    _ ≤ A.ncard+B.ncard := Set.ncard_union_le _ _
    _ ≤ 2^(m-2)*g (2^(m-2)) + 2^(m-2)*g (2^(m-2)) := Nat.add_le_add boundA boundB
    _ = _ := by rw [← Nat.two_mul, ← Nat.mul_assoc, ← pow_succ', show m-2+1 = m-1 by omega]

end OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1
