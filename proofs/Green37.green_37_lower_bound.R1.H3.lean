import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Step Green37.green_37_lower_bound.R1.H3
-- Credit: @caa1982

private lemma apCover_nonempty (N k : ℕ) :
    {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k}.Nonempty := by
  refine ⟨(Finset.range (k * N + 1)).card, Finset.range (k * N + 1), rfl, ?_⟩
  intro d ⟨hd1, hdN⟩
  refine ⟨0, {0 + n • d | (n : ℕ) (_ : n < (k : ℕ∞))}, ?_, ?_, rfl⟩
  · rintro x ⟨n, hn, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio, zero_add, smul_eq_mul]
    have hn' : n < k := by exact_mod_cast hn
    have hmul : n * d < k * d := Nat.mul_lt_mul_of_pos_right hn' (by omega)
    have hle : k * d ≤ k * N := Nat.mul_le_mul_left k hdN
    omega
  · have hinj : Function.Injective (fun n : Fin k => 0 + n.val • d) := by
      intro i j hij
      simp only [zero_add, smul_eq_mul] at hij
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) hij)
    have hset : {0 + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} =
        Set.range (fun n : Fin k => 0 + n.val • d) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_range]
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨n, by exact_mod_cast hn⟩, rfl⟩
      · rintro ⟨⟨n, hn⟩, rfl⟩
        exact ⟨n, by exact_mod_cast hn, rfl⟩
    rw [hset, ENat.card_congr (Equiv.ofInjective _ hinj).symm, ENat.card_eq_coe_natCard, Nat.card_fin]

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H3 := by
  constructor
  · intro N hN
    obtain ⟨A, hAcard, hAcov⟩ := Nat.sInf_mem (apCover_nonempty N 1)
    unfold Green37.m
    rw [← hAcard]
    obtain ⟨a, s, hsA, _, hseq⟩ := hAcov 1 ⟨le_rfl, hN⟩
    have ha : a ∈ A := by
      have has : a ∈ s := by
        rw [hseq]
        exact ⟨0, by norm_num, by simp⟩
      exact hsA has
    exact Finset.card_pos.mpr ⟨a, ha⟩
  · intro N
    obtain ⟨A, hAcard, hAcov⟩ := Nat.sInf_mem (apCover_nonempty N 2)
    unfold Green37.m
    rw [← hAcard]
    let L := (A ×ˢ A).filter (fun p => p.1 < p.2)
    let R := (A ×ˢ A).filter (fun p => p.2 < p.1)
    have hsub : Finset.Icc 1 N ⊆ L.image (fun p => p.2 - p.1) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      obtain ⟨a, s, hsA, _, hseq⟩ := hAcov d hd
      have haA : a ∈ A := by
        have : a ∈ s := by rw [hseq]; exact ⟨0, by norm_num, by simp⟩
        exact hsA this
      have hadA : a + d ∈ A := by
        have : a + d ∈ s := by rw [hseq]; exact ⟨1, by norm_num, by simp⟩
        exact hsA this
      rw [Finset.mem_image]
      refine ⟨(a, a + d), ?_, by omega⟩
      simp only [L, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨haA, hadA⟩, by omega⟩
    have hNle : N ≤ L.card := by
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Icc] at h1
      have h2 := Finset.card_image_le (s := L) (f := fun p : ℕ × ℕ => p.2 - p.1)
      omega
    have hLR : L.card = R.card := by
      have hswap : L.image Prod.swap = R := by
        ext ⟨x, y⟩
        simp only [L, R, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists,
          Prod.swap_prod_mk, Prod.mk.injEq]
        constructor
        · rintro ⟨a, b, ⟨⟨ha, hb⟩, hlt⟩, rfl, rfl⟩
          exact ⟨⟨hb, ha⟩, hlt⟩
        · rintro ⟨⟨hx, hy⟩, hlt⟩
          exact ⟨y, x, ⟨⟨hy, hx⟩, hlt⟩, rfl, rfl⟩
      rw [← hswap, Finset.card_image_of_injective _ Prod.swap_injective]
    have hdisj : Disjoint L R := by
      rw [Finset.disjoint_left]
      intro p hpL hpR
      simp only [L, R, Finset.mem_filter] at hpL hpR
      omega
    have hunion : L ∪ R = A.offDiag := by
      ext ⟨x, y⟩
      simp only [L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
      constructor
      · rintro (⟨⟨hx, hy⟩, hlt⟩ | ⟨⟨hx, hy⟩, hlt⟩) <;> exact ⟨hx, hy, by omega⟩
      · rintro ⟨hx, hy, hne⟩
        rcases lt_or_gt_of_ne hne with h | h
        · left; exact ⟨⟨hx, hy⟩, h⟩
        · right; exact ⟨⟨hx, hy⟩, h⟩
    have hoff : A.offDiag.card = A.card * (A.card - 1) := by
      rw [Finset.offDiag_card]
      rcases Nat.eq_zero_or_pos A.card with h0 | hpos
      · simp [h0]
      · rw [Nat.mul_sub_left_distrib, mul_one]
    have h2L : 2 * L.card = A.card * (A.card - 1) := by
      rw [← hoff, ← hunion, Finset.card_union_of_disjoint hdisj, ← hLR, two_mul]
    omega
