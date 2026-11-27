import OMAStatements.S_oeis_a330715

namespace OMA.P330715

open OMA.S_oeis_a330715

lemma a_rec (n : ℕ) : a (n + 4) = a (n + 3) % a (n + 1) + a (n + 2) + 1 := by rw [a]

lemma mod_help (A B r : ℕ) (h : A = B + r) (hr : r < B) : A % B = r := by
  rw [h, Nat.add_mod_left, Nat.mod_eq_of_lt hr]

lemma key : ∀ k : ℕ, a (2 * k + 6) = k ^ 2 + 3 ∧ a (2 * k + 7) = k ^ 2 + k + 4 ∧
    a (2 * k + 8) = (k + 1) ^ 2 + 3 ∧ a (2 * k + 9) = (k + 1) ^ 2 + (k + 1) + 4 := by
  intro k
  induction k with
  | zero => simp [a]
  | succ k ih =>
    obtain ⟨h6, h7, h8, h9⟩ := ih
    have e1 : 2 * (k + 1) + 6 = 2 * k + 8 := by ring
    have e2 : 2 * (k + 1) + 7 = 2 * k + 9 := by ring
    have e3 : 2 * (k + 1) + 8 = 2 * k + 6 + 4 := by ring
    have e4 : 2 * (k + 1) + 9 = 2 * k + 7 + 4 := by ring
    have h10 : a (2 * k + 6 + 4) = (k + 2) ^ 2 + 3 := by
      rw [a_rec]
      have m : a (2 * k + 6 + 3) % a (2 * k + 6 + 1) = 2 * k + 2 := by
        apply mod_help
        · show a (2 * k + 9) = a (2 * k + 7) + (2 * k + 2)
          rw [h9, h7]; ring
        · show 2 * k + 2 < a (2 * k + 7)
          rw [h7]; nlinarith [sq_nonneg (k : ℤ), Nat.zero_le k, Nat.le_self_pow (n := 2) (by norm_num) k]
      rw [m]
      show 2 * k + 2 + a (2 * k + 8) + 1 = (k + 2) ^ 2 + 3
      rw [h8]; ring
    have h11 : a (2 * k + 7 + 4) = (k + 2) ^ 2 + (k + 2) + 4 := by
      rw [a_rec]
      have m : a (2 * k + 7 + 3) % a (2 * k + 7 + 1) = 2 * k + 3 := by
        apply mod_help
        · show a (2 * k + 6 + 4) = a (2 * k + 8) + (2 * k + 3)
          rw [h10, h8]; ring
        · show 2 * k + 3 < a (2 * k + 8)
          rw [h8]; nlinarith [Nat.zero_le k]
      rw [m]
      show 2 * k + 3 + a (2 * k + 9) + 1 = (k + 2) ^ 2 + (k + 2) + 4
      rw [h9]; ring
    rw [e1, e2, e3, e4]
    exact ⟨h8, h9, h10, h11⟩

lemma even_case (k : ℕ) : a (2 * k + 6) = k ^ 2 + 3 := (key k).1
lemma odd_case (k : ℕ) : a (2 * k + 7) = k ^ 2 + k + 4 := (key k).2.1

end OMA.P330715

open OMA.S_oeis_a330715 OMA.P330715 in
theorem OMA.solution : type_of% @OMA.S_oeis_a330715.main := by
  constructor
  · intro n hn
    rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 5 := ⟨j - 5, by omega⟩
      have i0 : 2 * (k + 5) = 2 * (k + 2) + 6 := by ring
      have i1 : 2 * (k + 5) - 1 = 2 * (k + 1) + 7 := by omega
      have i3 : 2 * (k + 5) - 3 = 2 * k + 7 := by omega
      have i4 : 2 * (k + 5) - 4 = 2 * k + 6 := by omega
      rw [i1, i3, i4, i0, even_case, odd_case, odd_case, even_case]
      push_cast
      ring
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 5 := ⟨j - 5, by omega⟩
      have i0 : 2 * (k + 5) + 1 = 2 * (k + 2) + 7 := by ring
      have i1 : 2 * (k + 5) + 1 - 1 = 2 * (k + 2) + 6 := by omega
      have i3 : 2 * (k + 5) + 1 - 3 = 2 * (k + 1) + 6 := by omega
      have i4 : 2 * (k + 5) + 1 - 4 = 2 * k + 7 := by omega
      rw [i1, i3, i4, i0, odd_case, even_case, even_case, odd_case]
      push_cast
      ring
  · intro n hn
    rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
      have i0 : 2 * (k + 3) = 2 * k + 6 := by ring
      have hp : (-1 : ℤ) ^ (2 * (k + 3)) = 1 := by rw [pow_mul]; simp
      rw [hp, i0, even_case]
      push_cast
      ring
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
      have i0 : 2 * (k + 3) + 1 = 2 * k + 7 := by ring
      have hp : (-1 : ℤ) ^ (2 * (k + 3) + 1) = -1 := by rw [pow_succ, pow_mul]; simp
      rw [hp, i0, odd_case]
      push_cast
      ring
