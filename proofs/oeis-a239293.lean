import OMAStatements.S_oeis_a239293

theorem OMA_pw (n : ℕ) (hn : 1 ≤ n) : n ^ (n + 1) ≡ (if Odd (n + 1) then n else 1) [MOD n + 1] := by
  have h1 : (n : ℤ) ≡ -1 [ZMOD (n + 1 : ℕ)] := by
    rw [Int.modEq_iff_dvd]; exact ⟨-1, by push_cast; ring⟩
  split_ifs with ho
  · have := h1.pow (n + 1)
    rw [ho.neg_one_pow] at this
    have h2 : (n : ℤ) ^ (n + 1) ≡ n [ZMOD (n + 1 : ℕ)] := this.trans h1.symm
    exact_mod_cast h2
  · have he : Even (n + 1) := Nat.not_odd_iff_even.mp ho
    have := h1.pow (n + 1)
    rw [he.neg_one_pow] at this
    exact_mod_cast this

theorem OMA.solution : type_of% @OMA.S_oeis_a239293.main := by
  intro n hn
  unfold OMA.S_oeis_a239293.a
  have hpw := OMA_pw n hn
  constructor
  · intro h
    have hne : {c : ℕ | n < c ∧ OMA.S_oeis_a239293.IsComposite c ∧ n ^ c ≡ n [MOD c]}.Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      rw [hc] at h
      simp at h
    have hm := Nat.sInf_mem hne
    rw [h] at hm
    obtain ⟨_, hcomp, hmod⟩ := hm
    refine ⟨?_, hcomp⟩
    by_contra ho
    rw [if_neg ho] at hpw
    have h3 := hmod.symm.trans hpw
    have h4 : n ≡ 1 [MOD n + 1] := h3
    have h5 : (n + 1) ∣ n - 1 := (Nat.modEq_iff_dvd' hn).mp h4.symm
    have h7 : n - 1 = 0 := by
      by_contra hz
      have := Nat.le_of_dvd (by omega) h5
      omega
    have : n = 1 := by omega
    subst this
    exact hcomp.2 Nat.prime_two
  · rintro ⟨ho, hcomp⟩
    rw [if_pos ho] at hpw
    have hmem : n + 1 ∈ {c : ℕ | n < c ∧ OMA.S_oeis_a239293.IsComposite c ∧ n ^ c ≡ n [MOD c]} :=
      ⟨by omega, hcomp, hpw⟩
    apply le_antisymm (Nat.sInf_le hmem)
    have := Nat.sInf_mem ⟨_, hmem⟩
    exact this.1
