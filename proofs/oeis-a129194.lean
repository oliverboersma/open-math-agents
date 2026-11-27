import OMAStatements.S_oeis_a129194

namespace OMA.P_a129194

open OMA.S_oeis_a129194

/-- If `a, b` are coprime integers with `b > 0`, the denominator of `a / b` is `b`. -/
lemma den_eq (a b : ℤ) (hb : 0 < b) (h : IsCoprime a b) : (((a : ℚ) / b).den : ℚ) = b := by
  have h' : Nat.Coprime a.natAbs b.natAbs := Int.isCoprime_iff_gcd_eq_one.mp h
  have := Rat.den_div_eq_of_coprime hb h'
  exact_mod_cast this

theorem main : ∀ n : ℕ, 1 ≤ n → a n = (((4 : ℚ) / n - 2 / (n : ℚ) ^ 2).den : ℚ) := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : (m : ℚ) ≠ 0 := by have : 0 < m := by omega
                                exact_mod_cast this.ne'
    have heq : (4 : ℚ) / ((2 * m : ℕ) : ℚ) - 2 / ((2 * m : ℕ) : ℚ) ^ 2 =
        ((4 * m - 1 : ℤ) : ℚ) / ((2 * m ^ 2 : ℤ) : ℚ) := by
      push_cast
      field_simp
    have hc : IsCoprime (4 * (m : ℤ) - 1) (2 * (m : ℤ) ^ 2) := by
      apply IsCoprime.mul_right
      · exact ⟨-1, 2 * m, by ring⟩
      · apply IsCoprime.pow_right
        exact ⟨-1, 4, by ring⟩
    rw [heq, den_eq _ _ (by have : 0 < m := by omega
                            positivity) hc]
    simp only [a]; push_cast; rw [pow_mul]; norm_num; ring
  · have hm : (2 * (m : ℚ) + 1) ≠ 0 := by positivity
    have heq : (4 : ℚ) / ((2 * m + 1 : ℕ) : ℚ) - 2 / ((2 * m + 1 : ℕ) : ℚ) ^ 2 =
        ((8 * m + 2 : ℤ) : ℚ) / (((2 * m + 1) ^ 2 : ℤ) : ℚ) := by
      push_cast
      field_simp
      ring
    have hc : IsCoprime (8 * (m : ℤ) + 2) ((2 * (m : ℤ) + 1) ^ 2) := by
      apply IsCoprime.pow_right
      exact ⟨m, 1 - 4 * m, by ring⟩
    rw [heq, den_eq _ _ (by positivity) hc]
    simp only [a]; push_cast
    rw [pow_succ (-1 : ℚ), pow_mul]; norm_num; ring

end OMA.P_a129194

theorem OMA.solution : type_of% @OMA.S_oeis_a129194.main := OMA.P_a129194.main
