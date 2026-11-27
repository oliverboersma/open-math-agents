import OMAStatements.S_oeis_a152020

namespace OMA.P_a152020

open OMA.S_oeis_a152020

/-- If `a, b` are coprime integers with `b > 0`, the denominator of `a / b` is `b`. -/
lemma den_eq (a b : ℤ) (hb : 0 < b) (h : IsCoprime a b) : (((a : ℚ) / b).den : ℚ) = b := by
  have h' : Nat.Coprime a.natAbs b.natAbs := Int.isCoprime_iff_gcd_eq_one.mp h
  have := Rat.den_div_eq_of_coprime hb h'
  exact_mod_cast this

lemma two_cop (m : ℤ) : IsCoprime 2 (2 * m + 1) := ⟨-m, 1, by ring⟩

theorem main : ∀ n : ℕ, 1 ≤ n → a n = (((((n : ℚ) - 2) ^ 3) / (n : ℚ) ^ 2).den : ℚ) := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : 0 < m := by omega
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · -- n = 4k
      have hk : (k : ℚ) ≠ 0 := by have : 0 < k := by omega
                                  exact_mod_cast this.ne'
      have hk' : (0 : ℤ) < k := by omega
      have e1 : (8 : ℚ) / (9 * ((2 * (2 * k) : ℕ) : ℚ) ^ 2) =
          ((1 : ℤ) : ℚ) / ((18 * k ^ 2 : ℤ) : ℚ) := by
        push_cast; field_simp; try ring
      have e2 : ((((2 * (2 * k) : ℕ) : ℚ) - 2) ^ 3) / ((2 * (2 * k) : ℕ) : ℚ) ^ 2 =
          (((2 * k - 1) ^ 3 : ℤ) : ℚ) / ((2 * k ^ 2 : ℤ) : ℚ) := by
        push_cast; field_simp; try ring
      have c2 : IsCoprime ((2 * (k : ℤ) - 1) ^ 3) (2 * (k : ℤ) ^ 2) := by
        apply IsCoprime.pow_left
        apply IsCoprime.mul_right
        · exact ⟨-1, k, by ring⟩
        · exact IsCoprime.pow_right ⟨-1, 2, by ring⟩
      simp only [a]
      rw [e1, e2, den_eq _ _ (by positivity) isCoprime_one_left,
        den_eq _ _ (by positivity) c2]
      push_cast; ring
    · -- n = 2(2k+1)
      have hk : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
      have e1 : (8 : ℚ) / (9 * ((2 * (2 * k + 1) : ℕ) : ℚ) ^ 2) =
          ((2 : ℤ) : ℚ) / ((9 * (2 * k + 1) ^ 2 : ℤ) : ℚ) := by
        push_cast; field_simp; try ring
      have e2 : ((((2 * (2 * k + 1) : ℕ) : ℚ) - 2) ^ 3) / ((2 * (2 * k + 1) : ℕ) : ℚ) ^ 2 =
          ((16 * k ^ 3 : ℤ) : ℚ) / (((2 * k + 1) ^ 2 : ℤ) : ℚ) := by
        push_cast; field_simp; try ring
      have c1 : IsCoprime (2 : ℤ) (9 * (2 * k + 1) ^ 2) :=
        IsCoprime.mul_right ⟨-4, 1, by ring⟩ (IsCoprime.pow_right (two_cop k))
      have c2 : IsCoprime (16 * (k : ℤ) ^ 3) ((2 * (k : ℤ) + 1) ^ 2) := by
        apply IsCoprime.pow_right
        apply IsCoprime.mul_left
        · exact (show (16 : ℤ) = 2 ^ 4 by norm_num) ▸ IsCoprime.pow_left (two_cop k)
        · exact IsCoprime.pow_left ⟨-2, 1, by ring⟩
      simp only [a]
      rw [e1, e2, den_eq _ _ (by positivity) c1, den_eq _ _ (by positivity) c2]
      push_cast; ring
  · -- n = 2m+1
    have hm : (2 * (m : ℚ) + 1) ≠ 0 := by positivity
    have e1 : (8 : ℚ) / (9 * ((2 * m + 1 : ℕ) : ℚ) ^ 2) =
        ((8 : ℤ) : ℚ) / ((9 * (2 * m + 1) ^ 2 : ℤ) : ℚ) := by
      push_cast; ring
    have e2 : ((((2 * m + 1 : ℕ) : ℚ) - 2) ^ 3) / ((2 * m + 1 : ℕ) : ℚ) ^ 2 =
        (((2 * m - 1) ^ 3 : ℤ) : ℚ) / (((2 * m + 1) ^ 2 : ℤ) : ℚ) := by
      push_cast; ring
    have c1 : IsCoprime (8 : ℤ) (9 * (2 * m + 1) ^ 2) := by
      rw [show (8 : ℤ) = 2 ^ 3 by norm_num]
      exact IsCoprime.pow_left (IsCoprime.mul_right ⟨-4, 1, by ring⟩
        (IsCoprime.pow_right (two_cop m)))
    have c2 : IsCoprime ((2 * (m : ℤ) - 1) ^ 3) ((2 * (m : ℤ) + 1) ^ 2) :=
      IsCoprime.pow (⟨-m - 1, m, by ring⟩)
    simp only [a]
    rw [e1, e2, den_eq _ _ (by positivity) c1, den_eq _ _ (by positivity) c2]
    push_cast; ring

end OMA.P_a152020

theorem OMA.solution : type_of% @OMA.S_oeis_a152020.main := OMA.P_a152020.main
