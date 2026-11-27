import OMAStatements.S_oeis_a085781

-- Problem: A085781: a(n) = 2*binomial(2*n+1,n+1) - 2^n.
-- Upstream: formal-conjectures statements/oeis-a085781.lean:0 (declaration OMA.S_oeis_a085781.main)
-- Credit: @dreamzzz-dev (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a085781

theorem OMA.solution : type_of% @OMA.S_oeis_a085781.main := by
  intro n hn
  have central (j : ℕ) : Nat.centralBinom (j + 1) = 2 * (2 * j + 1).choose (j + 1) := by
    rw [Nat.centralBinom, show 2 * (j + 1) = (2 * j + 1) + 1 by omega,
      Nat.choose_succ_succ, Nat.choose_symm_half]
    exact (two_mul _).symm
  have term (j : ℕ) : a j = (Nat.centralBinom (j + 1) : ℤ) - 2 ^ j := by
    simp [a, central]
  have step (j : ℕ) :
      ((j : ℤ) + 1) * Nat.centralBinom (j + 1) =
        2 * (2 * (j : ℤ) + 1) * Nat.centralBinom j := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ j
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  simp only [term, Nat.cast_add, Nat.cast_ofNat, pow_add]
  have h3 := step (k + 3)
  have h2 := step (k + 2)
  have h1 := step (k + 1)
  push_cast at h3 h2 h1
  linear_combination h3 - 4 * h2 + 4 * h1
