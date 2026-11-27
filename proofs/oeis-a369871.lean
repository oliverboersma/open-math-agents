import OMAStatements.S_oeis_a369871

-- Problem: A369871, every prime is the least prime factor of infinitely many terms of A024411.
-- Credit: @bnb9001

namespace OMA_A369871_Proof

open OMA.S_oeis_a369871

/-- Euclid's formula, odd short leg `s t`. -/
lemma ppt_odd (s t A B : ℕ) (hst : Nat.Coprime s t) (ht0 : 0 < t) (h3 : 3 * t ≤ s)
    (hA : 2 * A + t ^ 2 = s ^ 2) (hB : 2 * B = s ^ 2 + t ^ 2) : IsPPT (s * t) A B := by
  have hB' : B = A + t ^ 2 := by omega
  have hs0 : 0 < s := by omega
  refine ⟨Nat.mul_pos hs0 ht0, ?_, ?_, ?_⟩
  · nlinarith
  · rw [hB', mul_pow, ← hA]; ring
  · apply Nat.Coprime.mul_left
    · apply Nat.coprime_of_dvd
      intro l hl hls hlA
      have h1 : l ∣ t ^ 2 := by
        have : t ^ 2 = s ^ 2 - 2 * A := by omega
        rw [this]; exact Nat.dvd_sub (dvd_pow hls two_ne_zero) (dvd_mul_of_dvd_right hlA 2)
      have hlt := hl.dvd_of_dvd_pow h1
      have := Nat.dvd_gcd hls hlt
      rw [hst] at this
      exact hl.one_lt.ne' (Nat.dvd_one.1 this)
    · apply Nat.coprime_of_dvd
      intro l hl hlt hlA
      have h1 : l ∣ s ^ 2 := by
        rw [← hA]; exact dvd_add (dvd_mul_of_dvd_right hlA 2) (dvd_pow hlt two_ne_zero)
      have hls := hl.dvd_of_dvd_pow h1
      have := Nat.dvd_gcd hls hlt
      rw [hst] at this
      exact hl.one_lt.ne' (Nat.dvd_one.1 this)

/-- Euclid's formula, even short leg `2 s t`. -/
lemma ppt_even (s t D : ℕ) (hst : Nat.Coprime s t) (hpar : (s + t) % 2 = 1) (ht0 : 0 < t)
    (h3 : 3 * t ≤ s) (hD : D + t ^ 2 = s ^ 2) : IsPPT (2 * s * t) D (D + 2 * t ^ 2) := by
  have hs0 : 0 < s := by omega
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · nlinarith
  · have : (2 * s * t) ^ 2 = 4 * t ^ 2 * s ^ 2 := by ring
    rw [this, ← hD]; ring
  · have hDodd : ¬ 2 ∣ D := by
      intro h2
      have hs2 : s ^ 2 % 2 = s % 2 := by rcases Nat.even_or_odd s with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega
      have ht2 : t ^ 2 % 2 = t % 2 := by rcases Nat.even_or_odd t with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega
      omega
    apply Nat.Coprime.mul_left
    · apply Nat.Coprime.mul_left
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hDodd
      · apply Nat.coprime_of_dvd
        intro l hl hls hlD
        have h1 : l ∣ t ^ 2 := by
          have : t ^ 2 = s ^ 2 - D := by omega
          rw [this]; exact Nat.dvd_sub (dvd_pow hls two_ne_zero) hlD
        have := Nat.dvd_gcd hls (hl.dvd_of_dvd_pow h1)
        rw [hst] at this
        exact hl.one_lt.ne' (Nat.dvd_one.1 this)
    · apply Nat.coprime_of_dvd
      intro l hl hlt hlD
      have h1 : l ∣ s ^ 2 := by rw [← hD]; exact dvd_add hlD (dvd_pow hlt two_ne_zero)
      have := Nat.dvd_gcd (hl.dvd_of_dvd_pow h1) hlt
      rw [hst] at this
      exact hl.one_lt.ne' (Nat.dvd_one.1 this)

lemma odd_sq_sub (s t : ℕ) (hs : s % 2 = 1) (ht : t % 2 = 1) (h : t ≤ s) :
    2 * ((s ^ 2 - t ^ 2) / 2) + t ^ 2 = s ^ 2 ∧ 2 * ((s ^ 2 + t ^ 2) / 2) = s ^ 2 + t ^ 2 := by
  have hs2 : s ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hs]
  have ht2 : t ^ 2 % 2 = 1 := by rw [Nat.pow_mod, ht]
  have hle : t ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left h 2
  omega

/-- For an odd prime `p`, there are arbitrarily large `m` with two triangles and `minFac m = p`. -/
lemma exists_odd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) :
    ∃ m, N < m ∧ MultiShortLeg m ∧ Nat.minFac m = p := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (p + N + 1)
  obtain ⟨r, hrge, hr⟩ := Nat.exists_infinite_primes (q + 1)
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hqodd : q % 2 = 1 := (hq.eq_two_or_odd).resolve_left (by omega)
  have hrodd : r % 2 = 1 := (hr.eq_two_or_odd).resolve_left (by omega)
  have cpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 (by omega)
  have cpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).2 (by omega)
  refine ⟨p * q * r, ?_, ?_, ?_⟩
  · have : q ≤ p * q * r := by
      calc q ≤ p * q := Nat.le_mul_of_pos_left q hp.pos
        _ ≤ p * q * r := Nat.le_mul_of_pos_right _ hr.pos
    omega
  · -- first triangle: s = p q r, t = 1
    have hs1 : (p * q * r) % 2 = 1 := by rw [Nat.mul_mod, Nat.mul_mod p q, hpodd, hqodd, hrodd]
    have hpq_le : p ≤ p * q * r :=
      (Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right _ hr.pos)
    have hge1 : 1 ≤ p * q * r := by omega
    obtain ⟨hA1, hB1⟩ := odd_sq_sub (p * q * r) 1 hs1 (by norm_num) hge1
    have T1 := ppt_odd (p * q * r) 1 _ _ (Nat.coprime_one_right _) one_pos (by omega) hA1 hB1
    rw [mul_one] at T1
    -- second triangle: s = q r, t = p
    have hs2 : (q * r) % 2 = 1 := by rw [Nat.mul_mod, hqodd, hrodd]
    have hpqr : p ≤ q * r := by nlinarith
    obtain ⟨hA2, hB2⟩ := odd_sq_sub (q * r) p hs2 hpodd hpqr
    have T2 := ppt_odd (q * r) p _ _ (Nat.Coprime.mul_right cpq cpr).symm hp.pos (by nlinarith) hA2 hB2
    rw [show q * r * p = p * q * r by ring] at T2
    refine ⟨_, _, _, _, T1, T2, fun heq => ?_⟩
    rw [heq] at hA1
    have : (q * r) ^ 2 * (p ^ 2 - 1) + 1 = p ^ 2 := by
      have e : (p * q * r) ^ 2 = p ^ 2 * (q * r) ^ 2 := by ring
      rw [e] at hA1
      have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
      zify [hp1] at hA1 hA2 ⊢
      nlinarith
    have hqr : 1 ≤ (q * r) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hq.pos hr.pos)
    have hp9 : 9 ≤ p ^ 2 := by nlinarith
    nlinarith
  · apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_of_dvd_left (dvd_mul_right p q) r))
    have hpq_le : p ≤ p * q * r :=
      (Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right _ hr.pos)
    have hmf := Nat.minFac_prime (show p * q * r ≠ 1 by omega)
    have hdvd := Nat.minFac_dvd (p * q * r)
    rcases (Nat.Prime.dvd_mul hmf).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hmf).1 h with h' | h'
      · exact le_of_eq ((Nat.prime_dvd_prime_iff_eq hmf hp).1 h').symm
      · rw [(Nat.prime_dvd_prime_iff_eq hmf hq).1 h']; omega
    · rw [(Nat.prime_dvd_prime_iff_eq hmf hr).1 h]; omega

lemma exists_two (N : ℕ) : ∃ m, N < m ∧ MultiShortLeg m ∧ Nat.minFac m = 2 := by
  obtain ⟨r, hrge, hr⟩ := Nat.exists_infinite_primes (N + 5)
  refine ⟨12 * r, by omega, ?_, ?_⟩
  · have h1 : 1 ^ 2 ≤ (6 * r) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have T1 := ppt_even (6 * r) 1 _ (Nat.coprime_one_right _) (by omega) one_pos (by omega)
      (Nat.sub_add_cancel h1)
    rw [show 2 * (6 * r) * 1 = 12 * r by ring] at T1
    have h3 : 3 ^ 2 ≤ (2 * r) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have c3 : Nat.Coprime (2 * r) 3 := by
      apply Nat.Coprime.mul_left
      · norm_num
      · exact (Nat.coprime_primes hr Nat.prime_three).2 (by omega)
    have T2 := ppt_even (2 * r) 3 _ c3 (by omega) (by norm_num) (by omega) (Nat.sub_add_cancel h3)
    rw [show 2 * (2 * r) * 3 = 12 * r by ring] at T2
    refine ⟨_, _, _, _, T1, T2, fun heq => ?_⟩
    have e1 : (6 * r) ^ 2 = 36 * r ^ 2 := by ring
    have e2 : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
    rw [e1, e2] at heq
    have : 9 ≤ 4 * r ^ 2 := by nlinarith
    omega
  · rw [Nat.minFac_eq_two_iff]; exact ⟨6 * r, by ring⟩

end OMA_A369871_Proof

open OMA_A369871_Proof OMA.S_oeis_a369871 in
theorem OMA.solution : type_of% @OMA.S_oeis_a369871.main := by
  classical
  intro p hp
  have hex : ∀ N, ∃ m, N < m ∧ MultiShortLeg m ∧ Nat.minFac m = p := by
    intro N
    by_cases h2 : p = 2
    · subst h2; exact exists_two N
    · exact exists_odd p hp h2 N
  set T := {m : ℕ | MultiShortLeg m ∧ Nat.minFac m = p} with hT
  have hTinf : T.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨B, hB⟩
    obtain ⟨m, hm, hmT⟩ := hex B
    have := hB hmT
    omega
  have himg : (fun m => Nat.count MultiShortLeg m + 1) '' T ⊆ {n : ℕ | 1 ≤ n ∧ a n = p} := by
    rintro _ ⟨m, ⟨hm, hmp⟩, rfl⟩
    refine ⟨by simp only; omega, ?_⟩
    simp only [a, Nat.add_sub_cancel, Nat.nth_count hm, hmp]
  refine Set.Infinite.mono himg (Set.Infinite.image ?_ hTinf)
  intro x hx y hy hxy
  exact Nat.count_injective hx.1 hy.1 (by simp only at hxy; omega)
