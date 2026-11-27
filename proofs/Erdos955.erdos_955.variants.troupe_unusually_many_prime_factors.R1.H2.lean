import OMAReductions.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1

-- Step Erdos955.erdos_955.variants.troupe_unusually_many_prime_factors.R1.H2
-- Credit: @caa1982

theorem OMA.solution : OMA.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1.H2 := by
  intro n hn hnp
  set p := n.minFac
  have hp_prime : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ n := Nat.minFac_dvd n
  have hp_sq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  set d := n / p
  have hpd : p * d = n := Nat.mul_div_cancel' hp_dvd
  have hd_pos : 0 < d := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp_prime.pos
  have hd_lt : d < n := by
    have : 2 ≤ p := hp_prime.two_le
    nlinarith
  have hd_dvd : d ∣ n := ⟨p, by rw [mul_comm, hpd]⟩
  have hsub : ({d, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨hd_dvd, by omega⟩
    · exact Nat.mem_divisors_self _ (by omega)
  have hsum : d + n ≤ ArithmeticFunction.sigma 1 n := by
    rw [ArithmeticFunction.sigma_one_apply]
    calc d + n = ∑ x ∈ ({d, n} : Finset ℕ), x := (Finset.sum_pair (f := fun x => x) hd_lt.ne).symm
      _ ≤ ∑ x ∈ n.divisors, x := Finset.sum_le_sum_of_subset hsub
  have hd_le_s : d ≤ Erdos955.s n := by
    unfold Erdos955.s
    omega
  have hp_le_d : p ≤ d := by
    have : p * p ≤ p * d := by rw [← sq, hpd]; exact hp_sq
    exact Nat.le_of_mul_le_mul_left this hp_prime.pos
  calc n = p * d := hpd.symm
    _ ≤ d * d := Nat.mul_le_mul_right d hp_le_d
    _ = d ^ 2 := (sq d).symm
    _ ≤ Erdos955.s n ^ 2 := Nat.pow_le_pow_left hd_le_s 2
