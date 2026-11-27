import OMAReductions.R_Erdos479_erdos_479_R1

-- Step Erdos479.erdos_479.R1.H1: hypothesis H1 of reduction Erdos479.erdos_479.R1
-- Credit: @ivillar
-- H1 := ∀ k : ℤ, (k = 0 ∨ k = -1 ∨ k = -2 ∨ ∃ i : ℕ, 1 ≤ i ∧ k = 2 ^ i) →     { n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }.Infinite

namespace OMA.E479H1

lemma mem_of_dvd {k : ℤ} {n : ℕ} (h : (n : ℤ) ∣ 2 ^ n - k) :
    (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] :=
  Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp h)

/-- `k = 0`: `n = 2 ^ j`. -/
lemma case_zero : { n : ℕ | (2 : ℤ) ^ n ≡ 0 [ZMOD (n : ℤ)] }.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ⟨2 ^ (a + 1), ?_, ?_⟩
  · show (2 : ℤ) ^ (2 ^ (a + 1)) ≡ 0 [ZMOD ((2 ^ (a + 1) : ℕ) : ℤ)]
    apply mem_of_dvd
    rw [sub_zero]
    push_cast
    exact pow_dvd_pow 2 (Nat.lt_two_pow_self).le
  · have : a + 1 < 2 ^ (a + 1) := Nat.lt_two_pow_self
    omega

/-- `3 ^ (j + 1) ∣ 2 ^ (3 ^ j) + 1`, by `x ^ 3 + 1 = (x + 1) (x ^ 2 - x + 1)`. -/
lemma three_pow_dvd (j : ℕ) : (3 : ℤ) ^ (j + 1) ∣ 2 ^ (3 ^ j) + 1 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    rw [show (3 : ℕ) ^ (j + 1) = 3 ^ j * 3 from pow_succ 3 j, pow_mul]
    generalize (2 : ℤ) ^ 3 ^ j = x at hc ⊢
    refine ⟨c * (3 ^ j * c * (3 ^ (j + 1) * c - 3) + 1), ?_⟩
    have hx : x = 3 ^ (j + 1) * c - 1 := by linarith
    subst hx
    ring

/-- `k = -1`: `n = 3 ^ j`. -/
lemma case_neg_one : { n : ℕ | (2 : ℤ) ^ n ≡ -1 [ZMOD (n : ℤ)] }.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ⟨3 ^ (a + 1), ?_, ?_⟩
  · show (2 : ℤ) ^ (3 ^ (a + 1)) ≡ -1 [ZMOD ((3 ^ (a + 1) : ℕ) : ℤ)]
    apply mem_of_dvd
    push_cast
    rw [sub_neg_eq_add]
    exact (pow_dvd_pow 3 (Nat.le_succ (a + 1))).trans (three_pow_dvd (a + 1))
  · have h1 : a + 1 < 2 ^ (a + 1) := Nat.lt_two_pow_self
    have h2 : 2 ^ (a + 1) ≤ 3 ^ (a + 1) := Nat.pow_le_pow_left (by norm_num) _
    omega

/-- Lehmer: if `n ≡ 2 (mod 4)`, `n ∣ 2 ^ n + 2` and `n - 1 ∣ 2 ^ n + 1`, then `m = 2 ^ n + 2`
has the same three properties. -/
lemma lehmer_step (n : ℕ) (h4 : n % 4 = 2) (h1 : n ∣ 2 ^ n + 2) (h2 : n - 1 ∣ 2 ^ n + 1) :
    (2 ^ n + 2) % 4 = 2 ∧ 2 ^ n + 2 ∣ 2 ^ (2 ^ n + 2) + 2 ∧
      2 ^ n + 2 - 1 ∣ 2 ^ (2 ^ n + 2) + 1 := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  have hp : 2 ^ (n' + 2) = 4 * 2 ^ n' := by ring
  refine ⟨by omega, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := h2
    have hs' : 2 ^ (n' + 2) + 1 = (n' + 1) * s := by simpa using hs
    have hodd : Odd ((n' + 1) * s) := by
      rw [← hs']
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    have hsodd : Odd s := (Nat.odd_mul.mp hodd).2
    have key : 2 ^ (n' + 1) + 1 ∣ 2 ^ (2 ^ (n' + 2) + 1) + 1 := by
      rw [hs', pow_mul]
      simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ (n' + 1)) 1 hsodd
    have e1 : 2 ^ (n' + 2) + 2 = 2 * (2 ^ (n' + 1) + 1) := by ring
    have e2 : 2 ^ (2 ^ (n' + 2) + 2) + 2 = 2 * (2 ^ (2 ^ (n' + 2) + 1) + 1) := by ring
    rw [e2, e1]
    exact mul_dvd_mul_left 2 key
  · obtain ⟨t, ht⟩ := h1
    have htodd : Odd t := by
      rw [Nat.odd_iff]
      by_contra hne
      have h2t : t % 2 = 0 := by omega
      have hm := Nat.mul_mod (n' + 2) t 4
      rw [← ht, h4] at hm
      omega
    have e : 2 ^ (n' + 2) + 2 - 1 = 2 ^ (n' + 2) + 1 := by omega
    rw [e, ht, pow_mul]
    simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ (n' + 2)) 1 htodd

lemma lehmer_exists (a : ℕ) :
    ∃ n, a < n ∧ n % 4 = 2 ∧ n ∣ 2 ^ n + 2 ∧ n - 1 ∣ 2 ^ n + 1 := by
  induction a with
  | zero => exact ⟨6, by norm_num, by norm_num, by norm_num, by norm_num⟩
  | succ a ih =>
    obtain ⟨n, han, h4, h1, h2⟩ := ih
    obtain ⟨e4, e1, e2⟩ := lehmer_step n h4 h1 h2
    refine ⟨2 ^ n + 2, ?_, e4, e1, e2⟩
    have : n < 2 ^ n := Nat.lt_two_pow_self
    omega

/-- `k = -2`: Lehmer's sequence `6, 66, 2 ^ 66 + 2, ...`. -/
lemma case_neg_two : { n : ℕ | (2 : ℤ) ^ n ≡ -2 [ZMOD (n : ℤ)] }.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨n, han, -, h1, -⟩ := lehmer_exists a
  refine ⟨n, ?_, han⟩
  show (2 : ℤ) ^ n ≡ -2 [ZMOD (n : ℤ)]
  apply mem_of_dvd
  rw [sub_neg_eq_add]
  exact_mod_cast h1

/-- Euler for the base `2`: an odd `m` divides `2 ^ φ m - 1`. -/
lemma euler_two (m : ℕ) (hm : Odd m) : (m : ℤ) ∣ 2 ^ Nat.totient m - 1 := by
  have h := Nat.ModEq.pow_totient (x := 2) (n := m) (Nat.coprime_two_left.mpr hm)
  have := Nat.modEq_iff_dvd.mp h
  push_cast at this
  exact dvd_sub_comm.mp this

/-- `k = 2 ^ i`: `n = i p` for primes `p > i` with `p ≡ 1 (mod φ b)`, where `i = 2 ^ e b`
with `b` odd. Then `n ∣ 2 ^ i (2 ^ (i (p - 1)) - 1) = 2 ^ n - 2 ^ i`. -/
lemma case_two_pow (i : ℕ) (hi : 1 ≤ i) :
    { n : ℕ | (2 : ℤ) ^ n ≡ 2 ^ i [ZMOD (n : ℤ)] }.Infinite := by
  obtain ⟨e, b, hb, hib⟩ := Nat.exists_eq_two_pow_mul_odd (show i ≠ 0 by omega)
  have hb0 : 0 < b := hb.pos
  have htot : Nat.totient b ≠ 0 := (Nat.totient_pos.mpr hb0).ne'
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨p, hp, hpgt, hpmod⟩ := Nat.exists_prime_gt_modEq_one (a + i + 2) htot
  refine ⟨i * p, ?_, ?_⟩
  · show (2 : ℤ) ^ (i * p) ≡ 2 ^ i [ZMOD ((i * p : ℕ) : ℤ)]
    apply mem_of_dvd
    have hbi : b ≤ i := by
      rw [hib]; exact Nat.le_mul_of_pos_left b (by positivity)
    have hcop : IsCoprime (b : ℤ) (p : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      apply Nat.Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      have := Nat.le_of_dvd hb0 hd
      omega
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    have hfac : (2 : ℤ) ^ (i * (q + 1)) - 2 ^ i = 2 ^ i * (2 ^ (i * q) - 1) := by ring
    rw [hfac]
    have hn : ((i * (q + 1) : ℕ) : ℤ) = 2 ^ e * ((b : ℤ) * ((q + 1 : ℕ) : ℤ)) := by
      rw [hib]; push_cast; ring
    rw [hn]
    apply mul_dvd_mul
    · apply pow_dvd_pow
      have h1 : 2 ^ e ≤ i := by rw [hib]; exact Nat.le_mul_of_pos_right _ hb0
      have h2 : e < 2 ^ e := Nat.lt_two_pow_self
      omega
    · apply hcop.mul_dvd
      · have hphi : Nat.totient b ∣ q := by
          have := (Nat.modEq_iff_dvd' (by omega : 1 ≤ q + 1)).mp hpmod.symm
          simpa using this
        obtain ⟨c, hc⟩ := Dvd.dvd.mul_left hphi i
        rw [hc]
        exact (euler_two b hb).trans (pow_one_sub_dvd_pow_mul_sub_one 2 _ _)
      · have hpodd : Odd (q + 1) := hp.odd_of_ne_two (by omega)
        have hfer := euler_two (q + 1) hpodd
        rw [Nat.totient_prime hp, Nat.add_sub_cancel] at hfer
        rw [mul_comm i q]
        exact hfer.trans (pow_one_sub_dvd_pow_mul_sub_one 2 _ _)
  · have : p ≤ i * p := Nat.le_mul_of_pos_left p (by omega)
    omega

end OMA.E479H1

theorem OMA.solution : OMA.R_Erdos479_erdos_479_R1.H1 := by
  unfold OMA.R_Erdos479_erdos_479_R1.H1
  rintro k (rfl | rfl | rfl | ⟨i, hi, rfl⟩)
  · exact OMA.E479H1.case_zero
  · exact OMA.E479H1.case_neg_one
  · exact OMA.E479H1.case_neg_two
  · exact OMA.E479H1.case_two_pow i hi
