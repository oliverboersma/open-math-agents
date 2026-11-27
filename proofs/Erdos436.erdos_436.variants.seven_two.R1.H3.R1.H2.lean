import OMAReductions.R_Erdos436_erdos_436_variants_seven_two_R1_H3_R1

/-! The seventh power criterion in a prime field: a nonzero residue is a seventh power
exactly when its (p-1)/7-th power is one. The converse writes the residue as a power of a
generator of the cyclic unit group. -/

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_seven_two_R1_H3_R1.H2 := by
  intro p hp h7 a ha
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := h7
  have hm0 : 0 < m := by
    have h2 := hp.two_le
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm
      omega
    · exact h
  have hdiv : (p - 1) / 7 = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m (by norm_num)
  rw [hdiv]
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x ≠ 0 := by
      rintro rfl
      simp at ha
    rw [← pow_mul, ← hm]
    exact ZMod.pow_card_sub_one_eq_one hx
  · intro h
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hord : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg (Units.mk0 a ha))
    have hu1 : (Units.mk0 a ha) ^ m = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, h, Units.val_one]
    have h2 : g ^ (k * (m : ℤ)) = 1 := by
      rw [zpow_mul, hk, zpow_natCast, hu1]
    have h3 : ((orderOf g : ℕ) : ℤ) ∣ k * m := orderOf_dvd_iff_zpow_eq_one.2 h2
    rw [hord, hm] at h3
    push_cast at h3
    have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm0.ne'
    have h4 : (7 : ℤ) ∣ k := (mul_dvd_mul_iff_right hmz).1 h3
    obtain ⟨j, rfl⟩ := h4
    refine ⟨((g ^ j : (ZMod p)ˣ) : ZMod p), ?_⟩
    have h5 : (g ^ j) ^ 7 = Units.mk0 a ha := by
      rw [← hk, ← zpow_natCast (g ^ j) 7, ← zpow_mul]
      congr 1
      push_cast
      ring
    have h6 := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) h5
    simpa using h6
