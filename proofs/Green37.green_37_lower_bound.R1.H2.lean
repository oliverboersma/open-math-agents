import OMAReductions.R_Green37_green_37_lower_bound_R1

/-! A cover for progressions of length `k₂` is also a cover for any `k₁ ≤ k₂` (truncate each
progression), and covers always exist, so the minimum is monotone in the length. -/

lemma ap_set_eq (a d k : ℕ) :
    ({x | ∃ (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞)), a + n • d = x} : Set ℕ) =
      ↑((Finset.range k).image fun n => a + n * d) := by
  ext x; simp [smul_eq_mul]

lemma ap_isAP (a d k : ℕ) (hd : 1 ≤ d) :
    Set.IsAPOfLengthWith ({x | ∃ (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞)), a + n • d = x} : Set ℕ)
      (k : ℕ∞) a d := by
  refine ⟨?_, rfl⟩
  have hinj : Function.Injective fun n => a + n * d := by
    intro m n h; simp only at h
    exact Nat.eq_of_mul_eq_mul_right hd (by omega)
  rw [ap_set_eq]
  simp [ENat.card_eq_coe_fintype_card, Finset.card_image_of_injective _ hinj]

/-- A progression of length `k₂` contains one of length `k₁ ≤ k₂` with the same difference. -/
lemma containsAP_mono {A : Set ℕ} {k₁ k₂ d : ℕ} (hk : k₁ ≤ k₂) (hd : 1 ≤ d)
    (h : A.ContainsAP k₂ d) : A.ContainsAP k₁ d := by
  obtain ⟨a, s, hsA, hs⟩ := h
  refine ⟨a, _, ?_, ap_isAP a d k₁ hd⟩
  rintro x ⟨n, hn, rfl⟩
  apply hsA
  rw [hs.eq]
  exact ⟨n, lt_of_lt_of_le hn (by exact_mod_cast hk), rfl⟩

/-- `{0, …, k N}` covers every difference `d ≤ N` with a progression of length `k`. -/
lemma cover_exists (N k : ℕ) :
    ∃ A : Finset ℕ, Green37.IsAPCover (A : Set ℕ) N k := by
  refine ⟨Finset.range (k * N + 1), fun d ⟨hd1, hdN⟩ => ⟨0, _, ?_, ap_isAP 0 d k hd1⟩⟩
  rintro x ⟨n, hn, rfl⟩
  have hn' : n < k := by exact_mod_cast hn
  simp only [Finset.coe_range, Set.mem_Iio, smul_eq_mul, zero_add]
  have : n * d ≤ k * N := Nat.mul_le_mul hn'.le hdN
  omega

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N k₁ k₂ hk
  unfold Green37.m
  have hne : { m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k₂ }.Nonempty := by
    obtain ⟨A, hA⟩ := cover_exists N k₂
    exact ⟨A.card, A, rfl, hA⟩
  obtain ⟨A, hcard, hA⟩ := Nat.sInf_mem hne
  rw [← hcard]
  exact Nat.sInf_le ⟨A, rfl, fun d hd => containsAP_mono hk hd.1 (hA d hd)⟩

