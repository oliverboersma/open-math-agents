import OMAReductions.R_Erdos456_erdos_456_variants_linniks_theorem_R1

/-! For n ≥ 1 take the prime l with n dividing l - 1 and l ≤ C n^L. It is 1 mod n, so it
belongs to the set whose infimum is p_n, and p_n ≤ l ≤ C n^L. -/

theorem OMA.solution : OMA.R_Erdos456_erdos_456_variants_linniks_theorem_R1.H2 := by
  intro C L h
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨l, hl, hdvd, hle⟩ := h n hn
  have hmod : l ≡ 1 [MOD n] := ((Nat.modEq_iff_dvd' hl.one_lt.le).2 hdvd).symm
  have hp : Erdos456.p n ≤ l := Nat.sInf_le ⟨hl, hmod⟩
  have hp' : (Erdos456.p n : ℝ) ≤ (l : ℝ) := by exact_mod_cast hp
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.rpow_natCast,
    Real.norm_of_nonneg (pow_nonneg hn0 L)]
  linarith
