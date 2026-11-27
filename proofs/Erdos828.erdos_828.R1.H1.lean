import OMAReductions.R_Erdos828_erdos_828_R1

-- Step Erdos828.erdos_828.R1.H1
-- Credit: @caa1982

theorem OMA.solution : OMA.R_Erdos828_erdos_828_R1.H1 := by
  intro a ha
  rcases ha with rfl | ⟨m, hm_pos, hphi_dvd, rfl⟩
  · rw [Set.infinite_iff_exists_gt]
    intro N
    refine ⟨2 ^ (N + 1), ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, add_zero]
      rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos N)]
      simp only [Nat.add_sub_cancel, show (2 : ℕ) - 1 = 1 by rfl, mul_one]
      have hdvd : 2 ^ N ∣ 2 ^ (N + 1) := Nat.pow_dvd_pow 2 (Nat.le_succ N)
      exact_mod_cast hdvd
    · have h1 : N < 2 ^ N := Nat.lt_two_pow_self
      have h2 : 2 ^ N ≤ 2 ^ (N + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ N)
      omega
  · rw [Set.infinite_iff_exists_gt]
    intro N
    obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (max N m + 1)
    have hpm : m < p := by omega
    have hcop : m.Coprime p := (Nat.coprime_of_lt_prime hm_pos.ne' hpm hp).symm
    refine ⟨m * p, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      rw [Nat.totient_mul hcop, Nat.totient_prime hp]
      have hsub : ((m * p : ℕ) : ℤ) + -(m : ℤ) = ((m * (p - 1) : ℕ) : ℤ) := by
        have hp1 : 1 ≤ p := hp.one_le
        push_cast [Nat.cast_sub hp1]
        ring
      rw [hsub]
      have hdvd : Nat.totient m * (p - 1) ∣ m * (p - 1) := Nat.mul_dvd_mul_right hphi_dvd (p - 1)
      exact_mod_cast hdvd
    · have hp_gt : N < p := by omega
      have hle : p ≤ m * p := Nat.le_mul_of_pos_left p hm_pos
      omega
