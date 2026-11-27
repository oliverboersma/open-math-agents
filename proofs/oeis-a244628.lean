import OMAStatements.S_oeis_a244628

namespace OMA.P_a244628

theorem main :
    ∀ p : ℕ, Nat.Prime p → (p % 8 = 3 ∨ p % 8 = 5) →
      2 ^ ((p - 1) / 2) % p = p - 1 := by
  intro p hp h8
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    omega
  have hns : ¬ IsSquare (2 : ZMod p) := by
    rw [ZMod.exists_sq_eq_two_iff hp2]; omega
  have hpow : (2 : ZMod p) ^ (p / 2) = -1 := by
    rcases ZMod.pow_div_two_eq_neg_one_or_one p h2 with h | h
    · exact absurd ((ZMod.euler_criterion p h2).mpr h) hns
    · exact h
  have hk : (p - 1) / 2 = p / 2 := by omega
  rw [hk]
  have hcast : (((2 ^ (p / 2) : ℕ)) : ZMod p) = -1 := by push_cast; exact hpow
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast] at hv
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  rw [hv, ZMod.val_neg_one]
  omega

end OMA.P_a244628

theorem OMA.solution : type_of% @OMA.S_oeis_a244628.main := OMA.P_a244628.main
