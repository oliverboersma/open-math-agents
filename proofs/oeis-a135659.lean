import OMAStatements.S_oeis_a135659
import Mathlib

lemma OMA.pw (j : ℕ) : 2 ^ (2 * j + 3) % 24 = 8 := by
  induction j with
  | zero => norm_num
  | succ i ih => rw [show 2 * (i + 1) + 3 = (2 * i + 3) + 2 by ring, pow_add]; omega

theorem OMA.solution : type_of% @OMA.S_oeis_a135659.main := by
  rintro m hm ⟨p, rfl⟩ h3
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' p
  · exfalso
    have h0 : ∀ i : ℕ, 2 ^ (2 * i) % 3 = 1 := by
      intro i
      induction i with
      | zero => norm_num
      | succ k ih => rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; omega
    have h4 : 3 ∣ 2 ^ (2 * j) - 1 := by have := h0 j; omega
    have := (Nat.Prime.eq_one_or_self_of_dvd hm 3 h4)
    omega
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by
      rcases j with _ | j
      · norm_num at h3
      · omega⟩
    have := OMA.pw i
    refine ⟨(2 ^ (2 * (i + 1) + 1) - 1) / 24, ?_⟩
    simp only [OMA.S_oeis_a135659.a]
    rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring] at *
    have : 8 ≤ 2 ^ (2 * i + 3) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * i + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
