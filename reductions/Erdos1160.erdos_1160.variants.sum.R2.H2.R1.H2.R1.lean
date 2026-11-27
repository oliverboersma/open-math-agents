import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1

-- Reduction Erdos1160.erdos_1160.variants.sum.R2.H2.R1.H2.R1 of step Erdos1160.erdos_1160.variants.sum.R2.H2.R1.H2
-- Credit: @gertjanvdgoot

/-!
Split the nilpotent orders n = 2^b * q (q odd, q > 1) with 7m/11 < b by the size of b.

* H1 (moderate two-part, b ≤ 3m/4): elementary. A nilpotent group is the product of its
  Sylow subgroups, the pc-presentation bound g(p^a)^6 ≤ p^(a^3) bounds every factor, and
  for b ≤ 3m/4 the total exponent is at most (c^3 + (1-c)^3 * 144/361)/6 * m^3 with c ≤ 3/4,
  about 0.0714 m^3, strictly below the Higman exponent 2/27 m^3 ≈ 0.0741 m^3 of g(2^(m-2)).
* H2 (large two-part, b > 3m/4): here the Sylow 2-subgroup has order 2^(m-2-s) with
  s < m/4, and the bound needs growth of g(2^k) between k = m-2-s and k = m-2, i.e. the
  sharp two-group enumeration (Li and Qiao, arXiv:2610.14509); this is the hard range.

main is a case split on 4 * v2(n) ≤ 3 * m.
-/

open Filter CategoryTheory Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1_H2_R1

/-- Nilpotent orders whose two-part exponent lies between 7m/11 and 3m/4. -/
def H1 : Prop := ∀ᶠ m : ℕ in atTop, ∀ n ∈ Finset.Ico 1 (2^m),
  (¬ ∃ k : ℕ, n = 2^k) → 7*m < 11*n.factorization 2 → 4*n.factorization 2 ≤ 3*m →
  (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsNilpotent G}).ncard ≤
    2^(m-2)*g (2^(m-2))

/-- Nilpotent orders whose two-part exponent exceeds 3m/4 (and is not all of n). -/
def H2 : Prop := ∀ᶠ m : ℕ in atTop, ∀ n ∈ Finset.Ico 1 (2^m),
  (¬ ∃ k : ℕ, n = 2^k) → 3*m < 4*n.factorization 2 →
  (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsNilpotent G}).ncard ≤
    2^(m-2)*g (2^(m-2))

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1.H2 := by
  intro moderate large
  filter_upwards [moderate, large] with m hmod hlarge
  intro n hn hnp hb
  by_cases h : 4 * n.factorization 2 ≤ 3 * m
  · exact hmod n hn hnp hb h
  · exact hlarge n hn hnp (by omega)

end OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1_H2_R1
