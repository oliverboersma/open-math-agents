import OMAStatements.S_oeis_a038867

/-! Every term is 2 modulo 3, while squares are 0 or 1 modulo 3.
Original checked proof by @sntntHb. Shorter proof by @caa1982. -/

open OMA.S_oeis_a038867 in
theorem OMA.solution : type_of% @OMA.S_oeis_a038867.main := by
  intro n ⟨k, hk⟩
  unfold a at hk
  rw [show (n + 5) ^ 3 = n ^ 3 + (3 * (5 * n ^ 2 + 25 * n) + 125) by ring,
    Nat.add_sub_cancel_left] at hk
  have h := congrArg (fun t : ℕ => (t : ZMod 3)) hk
  push_cast at h
  rw [show (3 : ZMod 3) = 0 by decide, zero_mul, zero_add,
    show (125 : ZMod 3) = 2 by decide] at h
  exact (by decide : ∀ x : ZMod 3, 2 ≠ x * x) _ h
