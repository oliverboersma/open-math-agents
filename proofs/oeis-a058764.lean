import OMAStatements.S_oeis_a058764

namespace OMA.S_oeis_a058764



/-- The entry's conjecture. -/
def Conjecture : Prop := ∀ n : ℕ, 1 < n → a n = 3 * 2 ^ (n - 1)

theorem witness (n : ℕ) (hn : 2 ≤ n) : cototient (3 * 2 ^ (n - 1)) = 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  unfold cototient
  have hcop : Nat.Coprime 3 (2 ^ (k + 1)) := Nat.Coprime.pow_right _ (by norm_num)
  rw [show k + 2 - 1 = k + 1 by omega, Nat.totient_mul hcop, Nat.totient_prime Nat.prime_three,
    Nat.totient_prime_pow_succ Nat.prime_two]
  have e1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have e2 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
  rw [e1, e2]
  omega

/-- An odd `m >= 3` with `φ(m)` not divisible by 4 satisfies `2m <= 3φ(m)`. -/
theorem odd_totient (m : ℕ) (hm : Odd m) (hm3 : 3 ≤ m) (h4 : ¬ 4 ∣ Nat.totient m) :
    2 * m ≤ 3 * Nat.totient m := by
  have hm1 : m ≠ 1 := by omega
  have hm0 : m ≠ 0 := by omega
  set p := m.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hm1
  have hpm : p ∣ m := Nat.minFac_dvd m
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpm
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hpm)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨e, r, hpr, hmr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hmr
    exact hpr (hmr ▸ hpm)
  have hcop : Nat.Coprime (p ^ e) r :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpr)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hmr; exact hm0 hmr
  by_cases hr1 : r = 1
  · subst hr1
    rw [mul_one] at hmr
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    rw [hmr, Nat.totient_prime_pow_succ hp, pow_succ]
    have : 2 * p ≤ 3 * (p - 1) := by omega
    calc 2 * (p ^ f * p) = p ^ f * (2 * p) := by ring
      _ ≤ p ^ f * (3 * (p - 1)) := Nat.mul_le_mul_left _ this
      _ = 3 * (p ^ f * (p - 1)) := by ring
  · exfalso
    have hrm : r ∣ m := ⟨p ^ e, by rw [hmr, mul_comm]⟩
    have hr_odd : Odd r := Odd.of_dvd_nat hm hrm
    have hr3 : 2 < r := by obtain ⟨i, hi⟩ := hr_odd; omega
    have hpe : 2 < p ^ e := by
      calc 2 < p := by omega
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos (by omega)
    obtain ⟨u, hu⟩ := Nat.totient_even hpe
    obtain ⟨v, hv⟩ := Nat.totient_even hr3
    apply h4
    rw [hmr, Nat.totient_mul hcop, hu, hv]
    exact ⟨u * v, by ring⟩

theorem lower (n : ℕ) (hn : 2 ≤ n) (x : ℕ) (hx : cototient x = 2 ^ n) : 3 * 2 ^ (n - 1) ≤ x := by
  unfold cototient at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
    exact absurd hx.symm (by positivity)
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hx0
  have hm0 : m ≠ 0 := by rintro rfl; simp at hx0
  have h2n : Even (2 ^ n) := (Nat.even_pow' (by omega)).2 even_two
  rcases k with _ | k
  · exfalso
    rw [pow_zero, one_mul] at hx
    have hm1 : m ≠ 1 := by
      rintro rfl
      simp at hx
      exact absurd hx.symm (by positivity)
    have hm2 : 2 < m := by obtain ⟨j, hj⟩ := hm; omega
    have he := Nat.totient_even hm2
    have hle := Nat.totient_le m
    have hsum : m = Nat.totient m + 2 ^ n := by omega
    have : Even m := by rw [hsum]; exact he.add h2n
    exact (Nat.not_even_iff_odd.2 hm) this
  · have hcop : Nat.Coprime (2 ^ (k + 1)) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
    rw [Nat.totient_mul hcop, Nat.totient_prime_pow_succ Nat.prime_two] at hx
    have hφm : Nat.totient m ≤ m := Nat.totient_le m
    have hc : 2 ^ k * (2 * m - Nat.totient m) = 2 ^ n := by
      rw [← hx, Nat.mul_sub, pow_succ]
      congr 1
      · ring
      · ring
    by_cases hm1 : m = 1
    · subst hm1
      rw [Nat.totient_one, show 2 * 1 - 1 = 1 by rfl, mul_one] at hc
      have hk : k = n := Nat.pow_right_injective (le_refl 2) hc
      subst hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [show j + 1 - 1 = j by omega, pow_succ, pow_succ]
      omega
    · have hm3 : 3 ≤ m := by obtain ⟨j, hj⟩ := hm; omega
      have hlt := Nat.totient_lt m (by omega)
      obtain ⟨j, hjn, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hc)
      have hcm : m < 2 * m - Nat.totient m := by omega
      have hj2 : 2 ≤ j := by
        rcases Nat.lt_or_ge j 2 with h | h
        · interval_cases j <;> simp at hj <;> omega
        · exact h
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
      have hc4 : 2 * m - Nat.totient m = 4 * 2 ^ i := by rw [hj]; ring
      have h4 : ¬ 4 ∣ Nat.totient m := by
        rintro ⟨t, ht⟩
        obtain ⟨s, hs⟩ := hm
        omega
      have h3 := odd_totient m hm hm3 h4
      have hmi : 3 * 2 ^ i ≤ m := by omega
      have hnk : n = k + (i + 2) := by
        rw [hc4, show 4 * 2 ^ i = 2 ^ (i + 2) by ring, ← pow_add] at hc
        exact (Nat.pow_right_injective (le_refl 2) hc).symm
      subst hnk
      rw [show k + (i + 2) - 1 = i + (k + 1) by omega, pow_add]
      calc 3 * (2 ^ i * 2 ^ (k + 1)) = (3 * 2 ^ i) * 2 ^ (k + 1) := by ring
        _ ≤ m * 2 ^ (k + 1) := Nat.mul_le_mul_right _ hmi
        _ = 2 ^ (k + 1) * m := by ring

theorem proof : Conjecture := by
  intro n hn
  refine le_antisymm (Nat.sInf_le (witness n hn)) (le_csInf ⟨_, witness n hn⟩ ?_)
  intro x hx
  exact lower n hn x hx

/-- Controls: `a(0) = 2` and `a(1) = 4`, as listed. -/
theorem a_eq_of {n v : ℕ} (hv : cototient v = 2 ^ n) (hmin : ∀ x < v, cototient x ≠ 2 ^ n) :
    a n = v :=
  le_antisymm (Nat.sInf_le hv) (le_csInf ⟨v, hv⟩ fun x hx => not_lt.mp fun h => hmin x h hx)

theorem a0 : a 0 = 2 := a_eq_of (by decide) (by decide)
theorem a1 : a 1 = 4 := a_eq_of (by decide) (by decide)

end OMA.S_oeis_a058764

theorem OMA.solution : type_of% @OMA.S_oeis_a058764.main :=
  OMA.S_oeis_a058764.proof
