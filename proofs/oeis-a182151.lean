import OMAStatements.S_oeis_a182151

open OMA.S_oeis_a182151

lemma three_pow_small : ∀ r < 30, (3 : ZMod 31) ^ r = 1 → r = 0 := by
  decide

lemma three_pow_30 : (3 : ZMod 31) ^ 30 = 1 := by
  decide

lemma dvd30 (k : ℕ) (hk : (3 : ZMod 31) ^ k = 1) : 30 ∣ k := by
  have h : k = 30 * (k / 30) + k % 30 := (Nat.div_add_mod k 30).symm
  rw [h, pow_add, pow_mul, three_pow_30, one_pow, one_mul] at hk
  exact Nat.dvd_of_mod_eq_zero (three_pow_small _ (Nat.mod_lt _ (by norm_num)) hk)

theorem OMA.solution : type_of% @OMA.S_oeis_a182151.main := by
  intro C hC h31
  obtain ⟨hC1, -, hferm⟩ := hC
  have : NeZero C := ⟨by omega⟩
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (n := 31) h31
    (ZMod.unitOfCoprime 3 (by norm_num))
  have hcop := ZMod.val_coe_unit_coprime u
  have hmod := (hferm _ hcop).of_dvd h31
  rw [← ZMod.natCast_eq_natCast_iff] at hmod
  push_cast at hmod
  have hval : (((u : ZMod C).val : ℕ) : ZMod 31) = 3 := by
    rw [ZMod.natCast_val]
    have := congrArg (fun v : (ZMod 31)ˣ => (v : ZMod 31)) hu
    simpa [ZMod.unitsMap] using this
  rw [hval] at hmod
  have h30 := dvd30 _ hmod
  obtain ⟨m, rfl⟩ := h31
  obtain ⟨k, hk⟩ := h30
  refine ⟨m / 90, ?_⟩
  omega
