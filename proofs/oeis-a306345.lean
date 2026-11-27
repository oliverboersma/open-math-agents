import OMAStatements.S_oeis_a306345

/-!
Source: https://oeis.org/A306345
Credit: @anmolspace (Lean formalization). Charlie Neder gave the divisor-count argument
in the OEIS entry in 2019. The proof below uses its parity to bound every factor.
-/

namespace OMA.A306345Proof

open OMA.S_oeis_a306345

/-- Positive divisors split into 1, primes, and composites. -/
private theorem balanced_iff {n : ℕ} (hn : 0 < n) :
    a n = 0 ↔ n.divisors.card = 2 * n.primeFactors.card + 1 := by
  have hsub : n.primeFactors ⊆ n.divisors.erase 1 := by
    intro p hp
    exact Finset.mem_erase.mpr ⟨(Nat.prime_of_mem_primeFactors hp).ne_one,
      Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hp, hn.ne'⟩⟩
  have hsize := Finset.card_le_card hsub
  have herase := Finset.card_erase_add_one (Nat.one_mem_divisors.mpr hn.ne')
  rw [a, Finset.card_sdiff_of_subset hsub]
  constructor
  · intro h
    have heq := Nat.eq_of_dist_eq_zero h
    omega
  · intro h
    apply Nat.dist_eq_zero
    omega

private theorem three_pow_bound (j : ℕ) : 2 * (j + 2) + 1 < 3 ^ (j + 2) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show j.succ + 2 = (j + 2) + 1 by omega, pow_succ]
    omega

/-- If the divisor counts agree, the odd total number of divisors forces each
prime exponent plus one to be at least three. Two distinct primes are already too many. -/
private theorem at_most_one_prime {n : ℕ} (hn : 0 < n)
    (h : n.divisors.card = 2 * n.primeFactors.card + 1) : n.primeFactors.card ≤ 1 := by
  have hprod := (Nat.card_divisors hn.ne').symm.trans h
  have hfactor : ∀ p ∈ n.primeFactors, 3 ≤ n.factorization p + 1 := by
    intro p hp
    have hpos := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn.ne'
      (Nat.dvd_of_mem_primeFactors hp)
    have hdvd := Finset.dvd_prod_of_mem (fun q => n.factorization q + 1) hp
    rw [hprod] at hdvd
    by_contra! hsmall
    have htwo : n.factorization p + 1 = 2 := by omega
    rw [htwo] at hdvd
    omega
  have hbound : 3 ^ n.primeFactors.card ≤ 2 * n.primeFactors.card + 1 := by
    calc
      _ = ∏ _p ∈ n.primeFactors, 3 := by simp
      _ ≤ _ := (Finset.prod_le_prod (fun _ _ => Nat.zero_le 3) hfactor).trans_eq hprod
  by_contra! hcard
  obtain ⟨j, hj⟩ : ∃ j, n.primeFactors.card = j + 2 := ⟨n.primeFactors.card - 2, by omega⟩
  rw [hj] at hbound
  exact (three_pow_bound j).not_ge hbound

end OMA.A306345Proof

open OMA.A306345Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a306345.main := by
  intro n hn
  rw [balanced_iff hn]
  constructor
  · intro h
    have hcard := at_most_one_prime hn h
    rcases Nat.eq_zero_or_pos n.primeFactors.card with hzero | hpos
    · left
      apply (Nat.divisors_card_eq_one_iff n).mp
      simpa [hzero] using h
    · right
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp (show n.primeFactors.card = 1 by omega)
      have hmem : p ∈ n.primeFactors := by simp [hp]
      have hprod := (Nat.card_divisors hn.ne').symm.trans h
      have hexp : n.factorization p = 2 := by
        simp [hp] at hprod
        omega
      exact ⟨p, Nat.prime_of_mem_primeFactors hmem,
        by simpa [hp, hexp] using Nat.prod_primeFactors_pow_factorization hn.ne'⟩
  · rintro (rfl | ⟨p, hp, rfl⟩)
    · simp
    · rw [← ArithmeticFunction.sigma_zero_apply,
        ArithmeticFunction.sigma_zero_apply_prime_pow hp, Nat.primeFactors_prime_pow (by decide) hp]
      simp
