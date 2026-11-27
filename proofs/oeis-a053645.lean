import OMAStatements.S_oeis_a053645

-- Problem: oeis-a053645
-- Credit: @LAPRAI (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @OMA.S_oeis_a053645.main := by
  refine ⟨by simp [OMA.S_oeis_a053645.a], ?_⟩
  intro n hn
  have hL1 : 2 ^ Nat.log 2 (n - 1) ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
  have hL2 : n - 1 < 2 ^ (Nat.log 2 (n - 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  unfold OMA.S_oeis_a053645.a OMA.S_oeis_a053645.a036987
  by_cases hp : ∃ k ≤ n - 1 + 1, n - 1 + 1 = 2 ^ k
  · rw [if_pos hp]
    obtain ⟨k, -, hk⟩ := hp
    have hn' : n = 2 ^ k := by omega
    rw [hn', Nat.log_pow (by norm_num)]
    simp
  · rw [if_neg hp]
    have hne : n ≠ 2 ^ (Nat.log 2 (n - 1) + 1) := by
      intro h
      apply hp
      refine ⟨Nat.log 2 (n - 1) + 1, ?_, by omega⟩
      have := @Nat.lt_two_pow_self (Nat.log 2 (n - 1) + 1)
      omega
    have hlog : Nat.log 2 n = Nat.log 2 (n - 1) :=
      Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
    rw [hlog]
    omega
