import OMAReductions.R_Green47_green_47_variants_finite_exceptions_R1
import Mathlib

-- Step Green47.green_47.variants.finite_exceptions.R1.H1: hypothesis H1 of reduction Green47.green_47.variants.finite_exceptions.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! If d is not a perfect square, some prime q divides d to an odd power. Using the Chinese
remainder theorem and quadratic reciprocity for the Jacobi symbol, build an odd b coprime to 4d
with J(d | b) = -1. By Dirichlet's theorem there are arbitrarily large primes p ≡ b mod 4d, and
J(d | p) = J(d | b) = -1 for them, so d is not a square modulo p. -/

open Filter



namespace Green47StepH1

lemma sq_of_even_fact (d : ℕ) (h : ∀ q, Even (d.factorization q)) : IsSquare d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨0, rfl⟩
  refine ⟨d.factorization.prod (fun p e => p ^ (e / 2)), ?_⟩
  rw [← Finsupp.prod_mul]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hd.ne']
  apply Finsupp.prod_congr
  intro p _
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := h p
  omega

lemma jac_one_of_modEq {r b : ℕ} (h : b ≡ 1 [MOD r]) : jacobiSym (b : ℤ) r = 1 := by
  have e : (b : ℤ) % r = (1 : ℤ) % r := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    simpa [Nat.ModEq, Int.natCast_mod] using this
  rw [jacobiSym.mod_left' e, jacobiSym.one_left]

lemma key (d : ℕ) (hd0 : d ≠ 0) (hd : ¬ IsSquare d) :
    ∃ b : ℕ, Odd b ∧ Nat.Coprime b (4 * d) ∧ jacobiSym (d : ℤ) b = -1 := by
  obtain ⟨q, hq⟩ : ∃ q, ¬ Even (d.factorization q) := by
    by_contra hc
    push Not at hc
    exact hd (sq_of_even_fact d hc)
  have hqo : Odd (d.factorization q) := Nat.not_even_iff_odd.mp hq
  have hqp : q.Prime := by
    by_contra hnp
    rw [Nat.factorization_eq_zero_of_not_prime d hnp] at hqo
    exact (Nat.not_odd_zero) hqo
  set e := d.factorization q with he
  set r := d / q ^ e with hr
  have hdr : d = q ^ e * r := (Nat.ordProj_mul_ordCompl_eq_self d q).symm
  have hqr : ¬ q ∣ r := Nat.not_dvd_ordCompl hqp hd0
  have hr0 : r ≠ 0 := by rintro h0; rw [h0, mul_zero] at hdr; exact hd0 hdr
  have hdz : (d : ℤ) = (q : ℤ) ^ e * (r : ℤ) := by rw [hdr]; push_cast; ring
  rcases hqp.eq_two_or_odd' with rfl | hqodd
  · -- q = 2, r odd
    have hrodd : Odd r := Nat.odd_iff.mpr (by
      have : ¬ 2 ∣ r := hqr
      omega)
    have hco : Nat.Coprime 8 r := by
      have : Nat.Coprime 2 r := (Nat.prime_two.coprime_iff_not_dvd).mpr hqr
      simpa using this.pow_left 3
    obtain ⟨b, hb8, hbr⟩ := Nat.chineseRemainder hco 5 1
    have hb8' : b % 8 = 5 := hb8
    have hbodd : Odd b := Nat.odd_iff.mpr (by omega)
    have hb4 : b % 4 = 1 := by omega
    refine ⟨b, hbodd, ?_, ?_⟩
    · have h2 : Nat.Coprime b 2 := (Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr
        (by omega)))
      have hbr' : Nat.Coprime b r := by
        rw [Nat.Coprime, Nat.ModEq.gcd_eq hbr]; simp
      rw [show 4 * d = 2 ^ (e + 2) * r by rw [hdr]; ring]
      exact Nat.Coprime.mul_right (h2.pow_right _) hbr'
    · rw [hdz]
      push_cast
      rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two hbodd]
      have hχ : ZMod.χ₈ (b : ZMod 8) = -1 := by
        rw [ZMod.χ₈_nat_mod_eight, hb8']; decide
      rw [hχ, hqo.neg_one_pow, jacobiSym.quadratic_reciprocity_one_mod_four' hrodd hb4,
        jac_one_of_modEq hbr]
      norm_num
  · -- q odd
    have hq2 : q ≠ 2 := by rintro rfl; norm_num at hqodd
    have := Fact.mk hqp
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by
      rw [ZMod.ringChar_zmod_n]; exact hq2)
    set n := a.val with hn
    have hna : (n : ZMod q) = a := ZMod.natCast_zmod_val a
    have hco : Nat.Coprime q (4 * r) := by
      apply Nat.Coprime.mul_right
      · have : Nat.Coprime q 2 := (Nat.coprime_primes hqp Nat.prime_two).mpr hq2
        simpa using this.pow_right 2
      · exact (hqp.coprime_iff_not_dvd).mpr hqr
    obtain ⟨b, hbq, hbr⟩ := Nat.chineseRemainder hco n 1
    have hb4 : b % 4 = 1 := by
      have := Nat.ModEq.of_mul_right r hbr
      have h1 : 1 % 4 = 1 := rfl
      unfold Nat.ModEq at this
      omega
    have hbodd : Odd b := Nat.odd_iff.mpr (by omega)
    have hbqcast : (b : ZMod q) = a := by
      rw [← hna]; exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hbq
    refine ⟨b, hbodd, ?_, ?_⟩
    · have hbq' : Nat.Coprime b q := by
        rw [Nat.coprime_comm, hqp.coprime_iff_not_dvd]
        intro hdvd
        apply ha
        rw [← hbqcast, (ZMod.natCast_eq_zero_iff b q).mpr hdvd]
        exact ⟨0, by simp⟩
      have hbr' : Nat.Coprime b (4 * r) := by
        rw [Nat.Coprime, Nat.ModEq.gcd_eq hbr]; simp
      rw [show 4 * d = q ^ e * (4 * r) by rw [hdr]; ring]
      exact Nat.Coprime.mul_right (hbq'.pow_right _) hbr'
    · rw [hdz, jacobiSym.mul_left, jacobiSym.pow_left]
      have hJr : jacobiSym (r : ℤ) b = 1 := by
        rw [jacobiSym.mod_right' r hbodd]
        have : b % (4 * r) = 1 := by
          have h1 : 1 % (4 * r) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [← h1]; exact hbr
        rw [this, jacobiSym.one_right]
      have hJq : jacobiSym (q : ℤ) b = -1 := by
        rw [jacobiSym.quadratic_reciprocity_one_mod_four' (hqp.odd_of_ne_two hq2) hb4]
        rw [ZMod.nonsquare_iff_jacobiSym_eq_neg_one]
        push_cast
        rw [hbqcast]
        exact ha
      rw [hJr, hJq, hqo.neg_one_pow]
      norm_num

theorem main : ∀ d : ℕ, (∀ᶠ p : ℕ in atTop, p.Prime → IsSquare (d : ZMod p)) → IsSquare d := by
  intro d h
  by_contra hd
  have hd0 : d ≠ 0 := by rintro rfl; exact hd ⟨0, rfl⟩
  obtain ⟨b, hbodd, hbcop, hJ⟩ := key d hd0 hd
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hcop : IsCoprime (b : ℤ) ((4 * d : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hbcop
  obtain ⟨p, hpN, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq N (by positivity) hcop
  have hpmod' : p % (4 * d) = b % (4 * d) := Int.natCast_modEq_iff.mp hpmod
  have hpodd : Odd p := by
    have h4 : p % 4 = b % 4 := by
      have := Nat.ModEq.of_mul_right d (show p ≡ b [MOD 4 * d] from hpmod')
      exact this
    have := Nat.odd_iff.mp hbodd
    exact Nat.odd_iff.mpr (by omega)
  have hJp : jacobiSym (d : ℤ) p = -1 := by
    rw [jacobiSym.mod_right' d hpodd, hpmod', ← jacobiSym.mod_right' d hbodd, hJ]
  have := Fact.mk hp
  have hns := ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp hJp
  apply hns
  simpa using hN p hpN.le hp

end Green47StepH1

theorem OMA.solution : OMA.R_Green47_green_47_variants_finite_exceptions_R1.H1 := Green47StepH1.main
