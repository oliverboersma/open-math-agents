import OMAStatements.S_oeis_a051960

-- Problem: oeis-a051960
-- Credit: @LAPRAI (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @OMA.S_oeis_a051960.main := by
  have key : ∀ k : ℕ, ((k : ℤ) + 2) * (catalan (k + 1) : ℤ) = 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by
    intro k
    have h1 : ((k : ℤ) + 1 + 1) * (catalan (k + 1) : ℤ) = (Nat.centralBinom (k + 1) : ℤ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom (k + 1)
    have h2 : ((k : ℤ) + 1) * (catalan k : ℤ) = (Nat.centralBinom k : ℤ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom k
    have h3 : ((k : ℤ) + 1) * (Nat.centralBinom (k + 1) : ℤ) =
        2 * (2 * (k : ℤ) + 1) * (Nat.centralBinom k : ℤ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    have h4 : ((k : ℤ) + 1) * (((k : ℤ) + 2) * (catalan (k + 1) : ℤ) -
        2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ)) = 0 := by
      linear_combination ((k : ℤ) + 1) * h1 + h3 - 2 * (2 * (k : ℤ) + 1) * h2
    rcases mul_eq_zero.1 h4 with h | h
    · have : (0 : ℤ) ≤ k := by positivity
      linarith
    · linarith
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  simp only [OMA.S_oeis_a051960.a]
  have hA := key m
  have hB := key (m + 1)
  push_cast at hA hB ⊢
  linear_combination (3 * (m : ℤ) + 8) * hB + 2 * (3 * (m : ℤ) + 2) * hA
