import OMAStatements.S_oeis_a337949

namespace OMA.S_oeis_a337949

lemma pow2_mod3 (k : ℕ) : 2 ^ k % 3 = if Even k then 1 else 2 := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [if_pos (even_two_mul m), pow_mul, Nat.pow_mod]; norm_num
  · rw [if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)), pow_succ, pow_mul,
      Nat.mul_mod, Nat.pow_mod]; norm_num

lemma e1 (n : ℕ) : (2 * n + 1) * (2 * n + 1 - 1) / 2 = n * (2 * n + 1) := by
  rw [show 2 * n + 1 - 1 = 2 * n by omega]
  rw [show (2 * n + 1) * (2 * n) = 2 * (n * (2 * n + 1)) by ring]; simp
lemma e2 (n : ℕ) : (2 * n + 1) * (2 * n + 1 + 1) / 2 = (2 * n + 1) * (n + 1) := by
  rw [show (2 * n + 1) * (2 * n + 1 + 1) = 2 * ((2 * n + 1) * (n + 1)) by ring]; simp
lemma e3 (n : ℕ) : (4 * n + 2) * (4 * n + 2 - 1) / 2 = (2 * n + 1) * (4 * n + 1) := by
  rw [show 4 * n + 2 - 1 = 4 * n + 1 by omega]
  rw [show (4 * n + 2) * (4 * n + 1) = 2 * ((2 * n + 1) * (4 * n + 1)) by ring]; simp
lemma e4 (n : ℕ) : (4 * n + 2) * (4 * n + 2 + 1) / 2 = (2 * n + 1) * (4 * n + 3) := by
  rw [show (4 * n + 2) * (4 * n + 2 + 1) = 2 * ((2 * n + 1) * (4 * n + 3)) by ring]; simp
lemma e5 (n : ℕ) : (4 * n + 4) * (4 * n + 4 - 1) / 2 = (2 * n + 2) * (4 * n + 3) := by
  rw [show 4 * n + 4 - 1 = 4 * n + 3 by omega]
  rw [show (4 * n + 4) * (4 * n + 3) = 2 * ((2 * n + 2) * (4 * n + 3)) by ring]; simp
lemma e6 (n : ℕ) : (4 * n + 4) * (4 * n + 4 + 1) / 2 = (2 * n + 2) * (4 * n + 5) := by
  rw [show (4 * n + 4) * (4 * n + 4 + 1) = 2 * ((2 * n + 2) * (4 * n + 5)) by ring]; simp

end OMA.S_oeis_a337949

open OMA.S_oeis_a337949 in
theorem OMA.solution : type_of% @OMA.S_oeis_a337949.main := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · rw [a, if_neg (by omega), e1, e2, Nat.add_mod, pow2_mod3, pow2_mod3]
    rcases Nat.even_or_odd n with h | h
    · have h1 : Even (n * (2 * n + 1)) := h.mul_right _
      have h2 : ¬ Even ((2 * n + 1) * (n + 1)) := by
        rw [Nat.not_even_iff_odd]; exact (odd_two_mul_add_one n).mul (h.add_one)
      simp [h1, h2]
    · have h1 : ¬ Even (n * (2 * n + 1)) := by
        rw [Nat.not_even_iff_odd]; exact h.mul (odd_two_mul_add_one n)
      have h2 : Even ((2 * n + 1) * (n + 1)) := h.add_one.mul_left _
      simp [h1, h2]
  · rw [a, if_neg (by omega), e3, e4, Nat.add_mod, pow2_mod3, pow2_mod3]
    have h1 : ¬ Even ((2 * n + 1) * (4 * n + 1)) := by
      rw [Nat.not_even_iff_odd]
      exact (odd_two_mul_add_one n).mul ⟨2 * n, by ring⟩
    have h2 : ¬ Even ((2 * n + 1) * (4 * n + 3)) := by
      rw [Nat.not_even_iff_odd]
      exact (odd_two_mul_add_one n).mul ⟨2 * n + 1, by ring⟩
    simp [h1, h2]
  · rw [a, if_neg (by omega), e5, e6, Nat.add_mod, pow2_mod3, pow2_mod3]
    have h1 : Even ((2 * n + 2) * (4 * n + 3)) := ⟨(n + 1) * (4 * n + 3), by ring⟩
    have h2 : Even ((2 * n + 2) * (4 * n + 5)) := ⟨(n + 1) * (4 * n + 5), by ring⟩
    simp [h1, h2]
