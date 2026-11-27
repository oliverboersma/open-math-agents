import OMAStatements.S_oeis_a009388

-- Problem: A009388: If a, b in sequence, so is a*b-1.
-- Upstream: formal-conjectures statements/oeis-a009388.lean:0 (declaration OMA.S_oeis_a009388.main)
-- Credit: @yuka30240 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a009388 in
theorem OMA.solution : type_of% @OMA.S_oeis_a009388.main := by
  have residues (x : ℕ) (hx : InSeq x) : x % 3 = 0 ∨ x % 3 = 2 := by
    induction hx with
    | base => decide
    | @step a b _ _ ha hb =>
      have h := Nat.mul_mod a b 3
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] at h <;> omega
  refine ⟨residues, ?_⟩
  intro n ⟨ha, hb, hc⟩
  have := residues _ ha
  have := residues _ hb
  have := residues _ hc
  omega

