import OMAStatements.S_oeis_a306362

lemma a_odd (k : ℕ) : OMA.S_oeis_a306362.b (2 * k + 1) = ((2 * k + 1 : ℕ) : ℤ) * (2 * (2 * k + 1 : ℕ) + 1) := by
  unfold OMA.S_oeis_a306362.b
  rw [pow_succ, pow_mul]
  push_cast
  norm_num
  exact Int.ediv_eq_of_eq_mul_right (by norm_num) (by ring)

lemma a_even (k : ℕ) : OMA.S_oeis_a306362.b (2 * k) = 1 + 2 * (k : ℤ) + 8 * (k : ℤ) ^ 2 := by
  unfold OMA.S_oeis_a306362.b
  rw [pow_mul]
  norm_num
  exact Int.ediv_eq_of_eq_mul_right (by norm_num) (by ring)

theorem OMA.solution : type_of% @OMA.S_oeis_a306362.main := by
  intro n hp h3
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [a_even] at hp h3 ⊢
    obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 5 ∧ k = 5 * j + r :=
      ⟨k / 5, k % 5, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 5).symm⟩
    push_cast
    rw [show (1 + 2 * (5 * (j : ℤ) + r) + 8 * (5 * (j : ℤ) + r) ^ 2)
        = (1 + 2 * (r : ℤ) + 8 * (r : ℤ) ^ 2) + 10 * (j + 20 * j ^ 2 + 8 * j * r) by ring]
    rw [Int.add_mul_emod_self_left]
    interval_cases r <;> norm_num
  · exfalso
    rw [a_odd] at hp h3
    rcases hp.irreducible.isUnit_or_isUnit rfl with hu | hu
    · rw [Int.isUnit_iff] at hu
      rcases hu with hu | hu
      · have hk : k = 0 := by omega
        subst hk
        norm_num at h3
      · omega
    · rw [Int.isUnit_iff] at hu
      omega
