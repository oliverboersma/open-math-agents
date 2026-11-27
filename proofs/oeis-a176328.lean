import OMAStatements.S_oeis_a176328
import Mathlib

namespace A176328

lemma eval_two (n : ℕ) : (Polynomial.bernoulli n).eval 2 = bernoulli' n + n := by
  have h := Polynomial.bernoulli_eval_one_add n 1
  rw [Polynomial.bernoulli_eval_one] at h
  have e : (1 : ℚ) + 1 = 2 := by norm_num
  rw [e] at h
  rw [h, one_pow, mul_one]

lemma num_half (k : ℕ) : ((-(2 * (k : ℚ) + 1)) / 2).num = -(2 * (k : ℤ) + 1) := by
  have hc : Nat.Coprime (-(2 * (k : ℤ) + 1)).natAbs (2 : ℤ).natAbs := by
    rw [Int.natAbs_neg]
    have e : (2 * (k : ℤ) + 1).natAbs = 2 * k + 1 := by omega
    rw [e]
    exact Nat.coprime_two_right.mpr ⟨k, rfl⟩
  have h := Rat.num_div_eq_of_coprime (a := -(2 * (k : ℤ) + 1)) (b := 2) (by norm_num) hc
  push_cast at h
  exact h

end A176328

theorem OMA.solution : type_of% @OMA.S_oeis_a176328.main := by
  intro n
  unfold OMA.S_oeis_a176328.a
  rw [Polynomial.bernoulli_eval_one, A176328.eval_two]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [bernoulli'_one]
  · have hz : bernoulli' (2 * n + 1) = 0 := bernoulli'_eq_zero_of_odd ⟨n, rfl⟩ (by omega)
    rw [hz]
    have e : ((-1 : ℚ) ^ (2 * n + 1) * (0 + (0 + ((2 * n + 1 : ℕ) : ℚ))) / 2) =
        (-(2 * (n : ℚ) + 1)) / 2 := by
      rw [pow_succ, pow_mul]
      push_cast
      norm_num
    rw [e, A176328.num_half]
