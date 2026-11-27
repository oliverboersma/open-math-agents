import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1_H1_R1
import Mathlib

-- Step Erdos78.erdos_78.variants.strongly_explicit.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction
-- Erdos78.erdos_78.variants.strongly_explicit.R1.H1.R1.H1.R1
-- Credit: @ivillar
--
-- Proof. 2 is not a cube in F_13, so X^(3^j) - 2 is irreducible (Mathlib, Kummer polynomials) and
-- R = F_13[X]/(X^(3^j) - 2) is a finite field with q = 13^(3^j) elements, q odd. Write h = q / 2.
-- Every nonzero a has a^h = 1 or -1, and a is a square iff a^h = 1 (Euler's criterion).
-- Since 13^(odd) = 13 mod 24, h = 6 mod 12, so 2^h = 2^6 = -1 in F_13: 2 is not a square in R.
-- Hence the root x (with x^(3^j) = 2) is not a square, so x^h = -1. For a non-square y,
-- y^h = -1 too, hence (x y)^h = 1 and x y is a square.

open Polynomial

namespace OMA.Erdos78H2

theorem two_not_cube : ∀ b : ZMod 13, b ^ 3 ≠ 2 := by decide

theorem two_ne_zero13 : (2 : ZMod 13) ≠ 0 := by decide

theorem key_pow (m : ℕ) (hm : Odd m) : (2 : ZMod 13) ^ (13 ^ m / 2) = -1 := by
  obtain ⟨r, rfl⟩ := hm
  have h1 : 169 ^ r % 24 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 13 ^ (2 * r + 1) = 13 * 169 ^ r := by
    rw [pow_succ, pow_mul, mul_comm]
    norm_num
  obtain ⟨s, hs⟩ : ∃ s, 169 ^ r = 24 * s + 1 := ⟨169 ^ r / 24, by omega⟩
  have h3 : 13 ^ (2 * r + 1) / 2 = 12 * (13 * s) + 6 := by
    rw [h2, hs]
    omega
  have e12 : (2 : ZMod 13) ^ 12 = 1 := by decide
  have e6 : (2 : ZMod 13) ^ 6 = -1 := by decide
  rw [h3, pow_add, pow_mul, e12, e6, one_pow, one_mul]

theorem main_aux (j : ℕ) (f : (ZMod 13)[X]) (hf : f = X ^ 3 ^ j - C 2) (y : AdjoinRoot f)
    (hy : ¬ IsSquare y) : IsSquare (AdjoinRoot.root f * y) := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hirr : Irreducible f := by
    rw [hf]
    exact X_pow_sub_C_irreducible_of_prime_pow Nat.prime_three (by norm_num) j two_not_cube
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  have hf0 : f ≠ 0 := hirr.ne_zero
  haveI : Module.Finite (ZMod 13) (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod 13)
  letI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot f) = 13 ^ 3 ^ j := by
    rw [Module.card_eq_pow_finrank (K := ZMod 13), ZMod.card,
      (AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hf, natDegree_X_pow_sub_C]
  have hodd3 : Odd (3 ^ j) := Odd.pow (by decide)
  have hoddq : Fintype.card (AdjoinRoot f) % 2 = 1 := by
    rw [hcard]
    exact Nat.odd_iff.mp (Odd.pow (by decide))
  have hchar : ringChar (AdjoinRoot f) ≠ 2 := by
    intro h
    have := (FiniteField.even_card_iff_char_two).mp h
    omega
  have hpm : ∀ a : AdjoinRoot f, a ≠ 0 →
      a ^ (Fintype.card (AdjoinRoot f) / 2) = 1 ∨ a ^ (Fintype.card (AdjoinRoot f) / 2) = -1 := by
    intro a ha
    have h1 : a ^ (Fintype.card (AdjoinRoot f) - 1) = 1 := FiniteField.pow_card_sub_one_eq_one a ha
    have h2 : Fintype.card (AdjoinRoot f) - 1 = (Fintype.card (AdjoinRoot f) / 2) * 2 := by omega
    rw [h2, pow_mul, sq] at h1
    exact mul_self_eq_one_iff.mp h1
  -- the root satisfies root ^ 3 ^ j = 2
  have hroot : (AdjoinRoot.root f) ^ 3 ^ j = 2 := by
    have h0 : AdjoinRoot.mk f (X ^ 3 ^ j - C 2) = 0 := by
      rw [← hf]
      exact AdjoinRoot.mk_self
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
    rw [h0]
    exact map_ofNat (AdjoinRoot.of f) 2
  have htwo0 : (2 : AdjoinRoot f) ≠ 0 := by
    intro h
    have h' : (AdjoinRoot.of f) (2 : ZMod 13) = (AdjoinRoot.of f) 0 := by
      rw [map_ofNat, map_zero]
      exact h
    exact two_ne_zero13 ((AdjoinRoot.of f).injective h')
  have hα0 : AdjoinRoot.root f ≠ 0 := by
    intro h
    rw [h, zero_pow (by positivity)] at hroot
    exact htwo0 hroot.symm
  have htwo : (2 : AdjoinRoot f) ^ (Fintype.card (AdjoinRoot f) / 2) = -1 := by
    rw [hcard]
    have h' : (AdjoinRoot.of f) ((2 : ZMod 13) ^ (13 ^ 3 ^ j / 2)) = (AdjoinRoot.of f) (-1) := by
      rw [key_pow _ hodd3]
    rw [map_pow, map_ofNat, map_neg, map_one] at h'
    exact h'
  have hneg : (-1 : AdjoinRoot f) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hchar
  have hαh : (AdjoinRoot.root f) ^ (Fintype.card (AdjoinRoot f) / 2) = -1 := by
    rcases hpm _ hα0 with h1 | h1
    · exfalso
      obtain ⟨β, hβ⟩ := (FiniteField.isSquare_iff hchar hα0).mpr h1
      have hsq : IsSquare (2 : AdjoinRoot f) := by
        refine ⟨β ^ 3 ^ j, ?_⟩
        rw [← hroot, hβ, mul_pow]
      have := (FiniteField.isSquare_iff hchar htwo0).mp hsq
      rw [htwo] at this
      exact hneg this
    · exact h1
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy ⟨0, by simp⟩
  have hyh : y ^ (Fintype.card (AdjoinRoot f) / 2) = -1 := by
    rcases hpm y hy0 with h1 | h1
    · exact absurd ((FiniteField.isSquare_iff hchar hy0).mpr h1) hy
    · exact h1
  have hprod : (AdjoinRoot.root f * y) ^ (Fintype.card (AdjoinRoot f) / 2) = 1 := by
    rw [mul_pow, hαh, hyh]
    norm_num
  exact (FiniteField.isSquare_iff hchar (mul_ne_zero hα0 hy0)).mpr hprod

end OMA.Erdos78H2

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1_H1_R1.H2 := by
  unfold OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1_H1_R1.H2
  intro j y hy
  exact OMA.Erdos78H2.main_aux j _ rfl y hy
