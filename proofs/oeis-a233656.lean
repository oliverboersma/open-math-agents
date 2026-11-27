import OMAStatements.S_oeis_a233656

open OMA.S_oeis_a233656

lemma a_closed (n : ℕ) : 2 * a n = 1 + 3 ^ n + 2 * n := by
  induction n with
  | zero => simp [a]
  | succ n ih => simp only [a]; push_cast; linear_combination 3 * ih

lemma a_period (n : ℕ) : a (n + 20) = a n + 10 * (3 ^ n * 174339220 + 2) := by
  have h1 := a_closed (n + 20)
  have h2 := a_closed n
  push_cast at h1
  have h : (2 : ℤ) * (a (n + 20) - (a n + 10 * (3 ^ n * 174339220 + 2))) = 0 := by
    linear_combination h1 - h2
  have := (mul_eq_zero.mp h).resolve_left (by norm_num)
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a233656.main := by
  refine ⟨?_, by decide⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 20 with h | h
    · interval_cases n <;> simp [a, pattern]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 20 := ⟨n - 20, by omega⟩
      rw [a_period, Int.add_mul_emod_self_left, ih m (by omega), Nat.add_mod_right]
