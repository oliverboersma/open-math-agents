import OMAReductions.R_Erdos436_erdos_436_variants_ge_four_R2
import Mathlib

-- Step Erdos436.erdos_436.variants.ge_four.R2.H2: hypothesis H2 of reduction Erdos436.erdos_436.variants.ge_four.R2
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Let R be the product of the odd primes r ≤ M. By the Chinese remainder theorem and Dirichlet's
theorem there are arbitrarily large primes p ≡ 5 mod 8 with p ≡ 1 mod R. For these, J(2 | p) = -1, so 2
is not a square mod p. Each odd prime r ≤ M is a square mod p because J(r | p) = J(p | r) = J(1 | r) = 1
by reciprocity, using p ≡ 1 mod 4. -/

open Erdos436

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_ge_four_R2.H2 := by
  intro M
  set S := (Finset.range (M + 1)).filter (fun r => r.Prime ∧ 2 < r) with hS
  set R := ∏ r ∈ S, r with hR
  have hcop : Nat.Coprime 8 R := by
    apply Nat.Coprime.prod_right
    intro r hr
    have hr' := (Finset.mem_filter.mp hr).2
    have h2 : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr'.1).mpr (by omega)
    simpa using h2.pow_left 3
  obtain ⟨c, hc8, hcR⟩ := Nat.chineseRemainder hcop 5 1
  have hc8' : c % 8 = 5 := hc8
  have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.mpr fun r hr => (Finset.mem_filter.mp hr).2.1.ne_zero
  have hccop : Nat.Coprime c (8 * R) := by
    apply Nat.Coprime.mul_right
    · have : Nat.Coprime c 2 := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
      simpa using this.pow_right 3
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq hcR]; simp
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hpN, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (max N M) (q := 8 * R)
    (by positivity) (Nat.isCoprime_iff_coprime.mpr hccop)
  have hpm : p % (8 * R) = c % (8 * R) := Int.natCast_modEq_iff.mp hpmod
  have hp8 : p % 8 = 5 := by
    have := Nat.ModEq.of_mul_right R (show p ≡ c [MOD 8 * R] from hpm)
    unfold Nat.ModEq at this; omega
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hp4 : p % 4 = 1 := by omega
  have := Fact.mk hp
  refine ⟨p, ⟨hp, ?_, ?_⟩, lt_of_le_of_lt (le_max_left _ _) hpN⟩
  · rintro ⟨-, x, hx⟩
    have hJ : jacobiSym 2 p = -1 := by
      rw [jacobiSym.at_two hpodd, ZMod.χ₈_nat_mod_eight, hp8]; decide
    have hns := (ZMod.nonsquare_iff_jacobiSym_eq_neg_one (a := 2) (p := p)).mp hJ
    apply hns
    refine ⟨x, ?_⟩
    have hx' : x ^ 2 = 2 := by exact_mod_cast hx
    push_cast
    rw [← hx', sq]
  · intro r hr hr2 hrM
    have hrS : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr, hr2⟩
    have hrR : r ∣ R := Finset.dvd_prod_of_mem _ hrS
    have hpr : p % r = 1 := by
      have h1 : p ≡ c [MOD r] :=
        Nat.ModEq.of_dvd hrR (Nat.ModEq.of_mul_left 8 (show p ≡ c [MOD 8 * R] from hpm))
      have h2 : c ≡ 1 [MOD r] := Nat.ModEq.of_dvd hrR hcR
      have h3 := h1.trans h2
      unfold Nat.ModEq at h3
      rw [h3]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨?_, ?_⟩
    · rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd hr.pos hdvd
      have := le_max_right N M
      omega
    · have hJ : jacobiSym (r : ℤ) p = 1 := by
        rw [jacobiSym.quadratic_reciprocity_one_mod_four' (hr.odd_of_ne_two (by omega)) hp4,
          jacobiSym.mod_left]
        have e : ((p : ℤ) % (r : ℤ)) = 1 := by exact_mod_cast hpr
        rw [e, jacobiSym.one_left]
      obtain ⟨y, hy⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
      exact ⟨y, by rw [sq]; exact_mod_cast hy.symm⟩
