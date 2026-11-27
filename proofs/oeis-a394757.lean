import OMAStatements.S_oeis_a394757

-- Problem: A394757: Numbers k in A014574 (averages of twin prime pairs) such that gcd(k, sigma(k)) is prime.
-- Upstream: formal-conjectures statements/oeis-a394757.lean:0 (declaration OMA.S_oeis_a394757.main)
-- Credit: @PandaWill (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A394757Proof

open ArithmeticFunction

/-- `1 + p` divides `1 + p + ... + p ^ (2t+1)`. -/
lemma sum_pow_dvd (p t : ℕ) : (1 + p) ∣ ∑ i ∈ Finset.range (2 * t + 2), p ^ i := by
  induction t with
  | zero => exact ⟨1, by simp [Finset.sum_range_succ]⟩
  | succ t ih =>
    rw [show 2 * (t + 1) + 2 = (2 * t + 2) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, add_assoc]
    exact dvd_add ih ⟨p ^ (2 * t + 2), by ring⟩

/-- If `sigma (p ^ n)` is coprime to `6`, then `n` is even. -/
lemma isSquare_prime_pow (p n : ℕ) (hp : p.Prime)
    (h : Nat.Coprime (sigma 1 (p ^ n)) 6) : IsSquare (p ^ n) := by
  rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact ⟨p ^ t, by ring⟩
  · exfalso
    rw [sigma_apply_prime_pow hp] at h
    simp only [mul_one] at h
    rw [show 2 * t + 1 + 1 = 2 * t + 2 by ring] at h
    have hd := sum_pow_dvd p t
    rcases hp.eq_two_or_odd' with rfl | hodd
    · have h3 := Nat.Coprime.coprime_dvd_left hd h
      exact absurd h3 (by decide)
    · have h2 : 2 ∣ ∑ i ∈ Finset.range (2 * t + 2), p ^ i := by
        refine dvd_trans ?_ hd
        rcases hodd with ⟨r, rfl⟩
        exact ⟨r + 1, by ring⟩
      have h3 := Nat.Coprime.coprime_dvd_left h2 h
      exact absurd h3 (by decide)

/-- If `sigma m` is coprime to `6`, then `m` is a perfect square. -/
lemma isSquare_of_coprime_six : ∀ m : ℕ, Nat.Coprime (sigma 1 m) 6 → IsSquare m := by
  intro m
  induction m using Nat.recOnPrimeCoprime with
  | zero => intro _; exact ⟨0, rfl⟩
  | prime_pow p n hp => exact isSquare_prime_pow p n hp
  | coprime a b _ _ hab ha hb =>
    intro h
    rw [isMultiplicative_sigma.map_mul_of_coprime hab] at h
    exact (ha (Nat.Coprime.coprime_mul_right h)).mul (hb (Nat.Coprime.coprime_mul_left h))

lemma sigma_two : sigma 1 2 = 3 := by
  rw [sigma_one_apply]; decide

lemma sigma_three : sigma 1 3 = 4 := by
  rw [sigma_one_apply]; decide

lemma sigma_four : sigma 1 4 = 7 := by
  rw [sigma_one_apply]; decide

end OMA.A394757Proof

open ArithmeticFunction OMA.A394757Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a394757.main := by
  intro k hk
  obtain ⟨h1, h2, hg⟩ := hk
  change (Nat.gcd k (sigma 1 k)).Prime at hg
  change 18 ∣ k ∧ (Nat.gcd k (sigma 1 k) = 2 ∨ Nat.gcd k (sigma 1 k) = 3)
  set g := Nat.gcd k (sigma 1 k) with hgdef
  -- a prime dividing both `k` and `sigma k` is `g`
  have key : ∀ q : ℕ, q.Prime → q ∣ k → q ∣ sigma 1 k → q = g := fun q hq hqk hqs =>
    (Nat.prime_dvd_prime_iff_eq hq hg).mp (Nat.dvd_gcd hqk hqs)
  have hk4 : k ≠ 4 := by
    rintro rfl
    rw [hgdef, sigma_four, show Nat.gcd 4 7 = 1 by rfl] at hg
    exact Nat.not_prime_one hg
  -- `k` is even
  have hk2 : 2 ∣ k := by
    by_contra hne
    have he : Even (k + 1) := by
      rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
      · exact absurd ⟨r, by omega⟩ hne
      · exact ⟨r + 1, by omega⟩
    have := (h2.even_iff).mp he
    have hk1 : k = 1 := by omega
    subst hk1
    exact Nat.not_prime_zero h1
  -- `3` divides `k`
  have hk3 : 3 ∣ k := by
    have hpos : 2 ≤ k - 1 := h1.two_le
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
    · omega
    · have hd : 3 ∣ k - 1 := by omega
      rcases h1.eq_one_or_self_of_dvd 3 hd with h' | h' <;> omega
    · have hd : 3 ∣ k + 1 := by omega
      rcases h2.eq_one_or_self_of_dvd 3 hd with h' | h' <;> omega
  have hkpos : 3 ≤ k := by have := h1.two_le; omega
  refine ⟨?_, ?_⟩
  · -- `9` divides `k`
    have hk9 : 9 ∣ k := by
      by_contra h9
      obtain ⟨j, rfl⟩ := hk3
      have hj : ¬ 3 ∣ j := fun ⟨r, hr⟩ => h9 ⟨r, by rw [hr]; ring⟩
      have hcop : Nat.Coprime 3 j := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hj
      have hs : sigma 1 (3 * j) = 4 * sigma 1 j := by
        rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_three]
      have hg2 : 2 = g := key 2 Nat.prime_two hk2 (by rw [hs]; exact Dvd.dvd.mul_right (by norm_num) _)
      -- `4` does not divide `k`
      have h4 : ¬ 4 ∣ 3 * j := by
        intro h4
        have : 4 ∣ g := Nat.dvd_gcd h4 (by rw [hs]; exact Dvd.intro _ rfl)
        rw [← hg2] at this
        norm_num at this
      obtain ⟨i, hi⟩ := hk2
      have hi2 : ¬ 2 ∣ i := fun ⟨r, hr⟩ => h4 ⟨r, by rw [hi, hr]; ring⟩
      have hcop2 : Nat.Coprime 2 i := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hi2
      have hs2 : sigma 1 (3 * j) = 3 * sigma 1 i := by
        rw [hi, isMultiplicative_sigma.map_mul_of_coprime hcop2, sigma_two]
      have hg3 : 3 = g := key 3 Nat.prime_three ⟨j, rfl⟩ (by rw [hs2]; exact Dvd.intro _ rfl)
      omega
    omega
  · by_cases hs2 : 2 ∣ sigma 1 k
    · exact Or.inl (key 2 Nat.prime_two hk2 hs2).symm
    by_cases hs3 : 3 ∣ sigma 1 k
    · exact Or.inr (key 3 Nat.prime_three hk3 hs3).symm
    exfalso
    have hc2 : Nat.Coprime (sigma 1 k) 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hs2).symm
    have hc3 : Nat.Coprime (sigma 1 k) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hs3).symm
    have hc6 : Nat.Coprime (sigma 1 k) 6 := by
      have := Nat.Coprime.mul_right hc2 hc3
      simpa using this
    obtain ⟨r, hr⟩ := isSquare_of_coprime_six k hc6
    -- `k = r * r`, so `k - 1 = (r - 1) * (r + 1)` is not prime
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by
      rcases r with _ | r
      · simp at hr; omega
      · simp⟩
    have hfac : k - 1 = s * (s + 2) := by rw [hr]; ring_nf; omega
    rw [hfac, Nat.prime_mul_iff] at h1
    rcases h1 with ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · subst h
      norm_num at hr
      exact hk4 hr
