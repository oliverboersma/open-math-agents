import OMAStatements.S_oeis_a346214

-- Problem: A346214: Triangular array read by rows. T(n,k) is the number of nilpotent n X n matrices over GF(2) with index k
-- Upstream: formal-conjectures statements/oeis-a346214.lean:0 (declaration OMA.S_oeis_a346214.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Refute the literal printed OEIS conjecture (with j < 2 * n) at n = 2, j = 1: LHS = 4 != 6 = RHS.

namespace OMA.Proof_oeis_a346214

open OMA.S_oeis_a346214

private lemma table_two_one : table 2 1 = 1 := by
  unfold table
  have hset :
      {M : BinaryMatrix 2 | 0 < 1 ∧ M ^ 1 = 0 ∧ ∀ i : ℕ, 0 < i → i < 1 → M ^ i ≠ 0} =
        {(0 : BinaryMatrix 2)} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, pow_one]
    constructor
    · rintro ⟨_, h0, _⟩
      exact h0
    · rintro rfl
      refine ⟨by decide, rfl, fun i hi1 hi2 => by omega⟩
  rw [hset, Set.ncard_singleton]

private lemma glOrder_one : glOrder 1 = 1 := by
  decide

private lemma glOrder_two : glOrder 2 = 6 := by
  decide

end OMA.Proof_oeis_a346214

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a346214.main) := by
  intro ⟨_, hfin⟩
  have h := hfin 2 1 (by decide) (by decide) (by decide)
  rw [show (2 : ℕ) - 1 = 1 by rfl, OMA.Proof_oeis_a346214.table_two_one,
    OMA.Proof_oeis_a346214.glOrder_one, OMA.Proof_oeis_a346214.glOrder_two] at h
  exact absurd h (by decide)
