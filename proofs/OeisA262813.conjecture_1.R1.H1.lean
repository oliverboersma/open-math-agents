import OMAReductions.R_OeisA262813_conjecture_1_R1
import Mathlib

/-! Step OeisA262813.conjecture_1.R1.H1. Credit: @ivillar (original proof). From 8 n + 1 = 8 x^3 + u^2 + 2 v^2, parity
modulo 8 forces u = 2 z + 1 and v = 2 y, hence n = x^3 + y^2 + T(z); z = 0 is excluded by 3 <= u
or by the nonsquare residual, so the term (x, y, z) of the sum defining a(n) equals 1. -/

namespace OMA262813H1

theorem main_H1 : OMA.R_OeisA262813_conjecture_1_R1.H1 := by
  intro n x u v hcase heq
  have hu : u % 2 = 1 := by
    rcases Nat.even_or_odd u with ⟨r, hr⟩ | ⟨r, hr⟩
    · subst hr
      have : 8 * n + 1 = 8 * x ^ 3 + 4 * r ^ 2 + 2 * v ^ 2 := by rw [heq]; ring
      omega
    · omega
  obtain ⟨z, rfl⟩ : ∃ z, u = 2 * z + 1 := ⟨u / 2, by omega⟩
  have hT : 2 * Nat.triangular z = z * (z + 1) := by
    unfold Nat.triangular; exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self z)
  have hv : v % 2 = 0 := by
    rcases Nat.even_or_odd v with ⟨w, hw⟩ | ⟨w, hw⟩
    · omega
    · subst hw
      have : 8 * n + 1 = 8 * x ^ 3 + 4 * (z * (z + 1)) + 1 + 8 * w ^ 2 + 8 * w + 2 := by
        rw [heq]; ring
      omega
  obtain ⟨y, rfl⟩ : ∃ y, v = 2 * y := ⟨v / 2, by omega⟩
  have hn : n = x ^ 3 + y ^ 2 + Nat.triangular z := by
    have : 8 * n + 1 = 8 * x ^ 3 + 4 * (z * (z + 1)) + 1 + 8 * y ^ 2 := by rw [heq]; ring
    omega
  have hz : 1 ≤ z := by
    rcases hcase with h3 | hns
    · omega
    · by_contra h0
      have hz0 : z = 0 := by omega
      subst hz0
      apply hns
      refine ⟨y, ?_⟩
      simp only [Nat.triangular, zero_mul, Nat.zero_div, add_zero] at hn
      rw [hn, Nat.add_sub_cancel_left, sq]
  have hx : x ≤ x ^ 3 := Nat.le_self_pow (by norm_num) x
  have hy : y ≤ y ^ 2 := Nat.le_self_pow (by norm_num) y
  have hzT : z ≤ Nat.triangular z := by nlinarith
  unfold OeisA262813.a
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨x, Finset.mem_range.mpr (by omega), ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨y, Finset.mem_range.mpr (by omega), ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨z, Finset.mem_Ico.mpr ⟨hz, by omega⟩, ?_⟩
  rw [if_pos (beq_iff_eq.mpr hn.symm)]
  norm_num

end OMA262813H1

theorem OMA.solution : OMA.R_OeisA262813_conjecture_1_R1.H1 := OMA262813H1.main_H1
