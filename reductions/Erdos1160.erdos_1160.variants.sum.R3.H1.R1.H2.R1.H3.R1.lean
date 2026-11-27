import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1
import Mathlib.GroupTheory.Solvable

/-!
Separate the odd order theorem from solvable group enumeration.
Credit: @Thomassien.

The first hypothesis is the Feit-Thompson theorem, restricted to the
bundled groups used by the original counting function. The second is the
solvable case of prescribed-Sylow enumeration after summing over profiles.
Pyber, Enumerating finite groups of given order, Ann. Math. 137 (1993),
203-220, gives uniform constants. The conclusion needs no particular
values of those constants.

This is a reduction, not an unconditional proof of the counting bound.
-/

open Finset Erdos1160 CategoryTheory

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R1

def H1 : Prop :=
  ∀ G : FiniteGrp.{0}, Odd (Nat.card G) → Group.IsSolvable G

def H2 : Prop :=
  ∃ C D : ℕ, ∀ n : ℕ, 0 < n →
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
    n^(C*(n.primeFactors.sup n.factorization)+D) *
      ∏ p ∈ n.primeFactors, g (p^n.factorization p)

lemma max_exponent_le {q r : ℕ} (hq : 0 < q) (hqr : q < 2^r) :
    q.primeFactors.sup q.factorization ≤ r := by
  apply Finset.sup_le
  intro p hp
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  have hpow : 2 ^ q.factorization p < 2^r :=
    lt_of_le_of_lt
      ((Nat.pow_le_pow_left hp2 _).trans
        (Nat.le_of_dvd hq (Nat.ordProj_dvd q p))) hqr
  exact ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpow).le

lemma overhead {q r μ C D : ℕ} (hqr : q ≤ 2^r) (hμ : μ ≤ r) :
    q^(C*μ+D) ≤ 2^((C+D)*(r+1)^2) := by
  calc
    q^(C*μ+D) ≤ (2^r)^(C*μ+D) := Nat.pow_le_pow_left hqr _
    _ = 2^(r*(C*μ+D)) := (pow_mul ..).symm
    _ ≤ 2^((C+D)*(r+1)^2) := by
      apply Nat.pow_le_pow_right (by decide)
      have hm := Nat.mul_le_mul_left (r*C) hμ
      nlinarith only [hm, Nat.zero_le (C*r), Nat.zero_le (D*r^2),
        Nat.zero_le (D*r), Nat.zero_le C, Nat.zero_le D]

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1.H3 := by
  rintro hodd ⟨C, D, hcount⟩
  refine ⟨C+D, fun q r ho hqr => ?_⟩
  have hq : 0 < q := by obtain ⟨k, hk⟩ := ho; omega
  have hset : {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G} =
      {G : FiniteGrp.{0} | Nat.card G = q} := by
    ext G
    exact ⟨And.left, fun hG => ⟨hG, hodd G (by rwa [hG])⟩⟩
  have hbound := hcount q hq
  rw [hset] at hbound
  change g q ≤ _ at hbound
  exact hbound.trans (Nat.mul_le_mul_right _
    (overhead hqr.le (max_exponent_le hq hqr)))

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R1
