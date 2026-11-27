import OMAStatements.S_oeis_a000188

theorem OMA.solution : type_of% @OMA.S_oeis_a000188.main := by
  intro n hn
  obtain ⟨r, q, hnqr, hr⟩ := Nat.sq_mul_squarefree n
  have hnpos : 0 < n := hn
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hnqr; omega
    · exact h
  have hr0 : 0 < r := hr.ne_zero.bot_lt
  have hnr : n = q ^ 2 * r := hnqr.symm
  have L : ((Finset.range n).filter (fun x => x * x % n = 0)) =
      (Finset.range q).image (fun y => q * r * y) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hx, h⟩
      have hd : n ∣ x ^ 2 := by rw [pow_two]; exact Nat.dvd_of_mod_eq_zero h
      rw [hnr] at hd
      have h1 : q ^ 2 ∣ x ^ 2 := Dvd.dvd.trans (Dvd.intro _ rfl) hd
      have h2 : q ∣ x := (Nat.pow_dvd_pow_iff (by norm_num)).mp h1
      obtain ⟨y, rfl⟩ := h2
      have h3 : r ∣ y ^ 2 := by
        have : q ^ 2 * r ∣ q ^ 2 * y ^ 2 := by rw [← mul_pow]; exact hd
        exact (Nat.mul_dvd_mul_iff_left (by positivity)).mp this
      have h4 : r ∣ y := (hr.dvd_pow_iff_dvd (by norm_num)).mp h3
      obtain ⟨z, rfl⟩ := h4
      refine ⟨z, ?_, by ring⟩
      rw [hnr] at hx
      have : q * r * z * 1 < q * r * q := by nlinarith
      nlinarith
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hnr]; nlinarith
      · apply Nat.mod_eq_zero_of_dvd
        exact ⟨r * y ^ 2, by rw [hnr]; ring⟩
  have R : ((Finset.Icc 1 n).filter (fun k => IsSquare (n * k))) =
      (Finset.Icc 1 q).image (fun m => r * m ^ 2) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, u, hu⟩
      rw [hnr] at hu
      have h1 : r * k = (u / q) ^ 2 := by
        have hqd : q ∣ u := by
          have : q ^ 2 ∣ u ^ 2 := ⟨r * k, by rw [pow_two u, ← hu]; ring⟩
          exact (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp this
        obtain ⟨w, rfl⟩ := hqd
        rw [Nat.mul_div_cancel_left _ hq]
        have : q ^ 2 * (r * k) = q ^ 2 * w ^ 2 := by rw [show q ^ 2 * (r * k) = q ^ 2 * r * k by ring, hu]; ring
        exact Nat.eq_of_mul_eq_mul_left (by positivity) this
      set w := u / q
      have h3 : r ∣ w ^ 2 := ⟨k, by rw [← h1]⟩
      have h4 : r ∣ w := (hr.dvd_pow_iff_dvd (by norm_num)).mp h3
      obtain ⟨v, hv⟩ := h4
      have hk : k = r * v ^ 2 := by
        rw [hv] at h1
        have : r * k = r * (r * v ^ 2) := by rw [h1]; ring
        exact Nat.eq_of_mul_eq_mul_left hr0 this
      refine ⟨v, ⟨?_, ?_⟩, hk.symm⟩
      · rcases Nat.eq_zero_or_pos v with h | h
        · subst h; simp at hk; omega
        · exact h
      · rw [hnr, hk] at hk2
        have : r * v ^ 2 ≤ r * q ^ 2 := by nlinarith
        have h5 : v ^ 2 ≤ q ^ 2 := Nat.le_of_mul_le_mul_left this hr0
        exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h5
    · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, q * m * r, ?_⟩
      · exact Nat.mul_pos hr0 (by positivity)
      · rw [hnr]
        have : m ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hm2 2
        nlinarith
      · rw [hnr]; ring
  rw [L, R, Finset.card_image_of_injective, Finset.card_image_of_injective]
  · simp
  · intro a b h
    simp only at h
    have : a ^ 2 = b ^ 2 := Nat.eq_of_mul_eq_mul_left hr0 h
    exact (Nat.pow_left_injective (by norm_num)) this
  · intro a b h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
