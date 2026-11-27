import OMAStatements.S_oeis_a337951

lemma pow16 (j : ℕ) : 4 ^ (2 * j) % 5 = 1 := by
  rw [pow_mul, Nat.pow_mod]; norm_num

lemma pow16' (j : ℕ) : 4 ^ (2 * j + 1) % 5 = 4 := by
  rw [pow_succ, Nat.mul_mod, pow16]

theorem OMA.solution : type_of% @OMA.S_oeis_a337951.main := by
  intro n
  unfold OMA.S_oeis_a337951.a
  refine ⟨?_, ?_, ?_⟩
  · rw [if_neg (by omega)]
    have e1 : (2 * n + 1) * (2 * n + 1 - 1) / 2 = n * (2 * n + 1) := by
      rw [show 2 * n + 1 - 1 = 2 * n by omega]
      rw [show (2 * n + 1) * (2 * n) = 2 * (n * (2 * n + 1)) by ring]; omega
    have e2 : (2 * n + 1) * (2 * n + 1 + 1) / 2 = (n + 1) * (2 * n + 1) := by
      rw [show (2 * n + 1) * (2 * n + 1 + 1) = 2 * ((n + 1) * (2 * n + 1)) by ring]; omega
    rw [e1, e2]
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      rw [show (k + k) * (2 * (k + k) + 1) = 2 * (k * (4 * k + 1)) by ring,
        show (k + k + 1) * (2 * (k + k) + 1) = 2 * (4 * k * k + 3 * k) + 1 by ring]
      unfold Nat.ModEq; rw [Nat.add_mod]; simp only [pow16, pow16']
    · subst hk
      rw [show (2 * k + 1) * (2 * (2 * k + 1) + 1) = 2 * (4 * k * k + 5 * k + 1) + 1 by ring,
        show (2 * k + 1 + 1) * (2 * (2 * k + 1) + 1) = 2 * ((k + 1) * (4 * k + 3)) by ring]
      unfold Nat.ModEq; rw [Nat.add_mod]; simp only [pow16, pow16']
  · rw [if_neg (by omega)]
    have e1 : (4 * n + 2) * (4 * n + 2 - 1) / 2 = 2 * (4 * n * n + 3 * n) + 1 := by
      rw [show 4 * n + 2 - 1 = 4 * n + 1 by omega]
      rw [show (4 * n + 2) * (4 * n + 1) = 2 * (2 * (4 * n * n + 3 * n) + 1) by ring]; omega
    have e2 : (4 * n + 2) * (4 * n + 2 + 1) / 2 = 2 * (4 * n * n + 5 * n + 1) + 1 := by
      rw [show (4 * n + 2) * (4 * n + 2 + 1) = 2 * (2 * (4 * n * n + 5 * n + 1) + 1) by ring]; omega
    rw [e1, e2]
    unfold Nat.ModEq; rw [Nat.add_mod]; simp only [pow16']
  · rw [if_neg (by omega)]
    have e1 : (4 * n + 4) * (4 * n + 4 - 1) / 2 = 2 * ((n + 1) * (4 * n + 3)) := by
      rw [show 4 * n + 4 - 1 = 4 * n + 3 by omega]
      rw [show (4 * n + 4) * (4 * n + 3) = 2 * (2 * ((n + 1) * (4 * n + 3))) by ring]; omega
    have e2 : (4 * n + 4) * (4 * n + 4 + 1) / 2 = 2 * ((n + 1) * (4 * n + 5)) := by
      rw [show (4 * n + 4) * (4 * n + 4 + 1) = 2 * (2 * ((n + 1) * (4 * n + 5))) by ring]; omega
    rw [e1, e2]
    unfold Nat.ModEq; rw [Nat.add_mod]; simp only [pow16]
