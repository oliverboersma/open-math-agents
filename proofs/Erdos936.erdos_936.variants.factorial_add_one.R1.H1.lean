import OMAReductions.R_Erdos936_erdos_936_variants_factorial_add_one_R1

-- Step Erdos936.erdos_936.variants.factorial_add_one.R1.H1: hypothesis H1 of reduction Erdos936.erdos_936.variants.factorial_add_one.R1
-- Credit: @NoahPuckett-IO
-- Write c as the product of p ^ v_p(c) over its prime factors; powerful means every v_p(c) is at least 2.

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1.H1 := by
  intro c hc hpow
  have hc0 : c ≠ 0 := by omega
  have e := Nat.prod_factorization_pow_eq_self hc0
  simp only [Finsupp.prod, Nat.support_factorization] at e
  have key : ∏ p ∈ c.primeFactors, p ^ 2 ∣ ∏ p ∈ c.primeFactors, p ^ c.factorization p := by
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact Nat.pow_dvd_pow p ((hpp.pow_dvd_iff_le_factorization hc0).1 (hpow p hp))
  rw [e] at key
  rw [← Finset.prod_pow]
  exact key
